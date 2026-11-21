import Shellsort.SourceDecomposition
import Shellsort.FiberEquivalences
import Mathlib.Data.Fintype.Powerset

/-! Exact finite occupancy multiplicity for a threshold subset and a
partition into predetermined gap chains. -/
noncomputable section
namespace Shellsort.ThresholdOccupancyLaw
open Finset
open scoped Classical

private abbrev Slice {α I : Type*} (f : α → I) (r : I) := {a : α // f a = r}

private def join {α I : Type*} [Fintype α] (f : α → I)
    (v : ∀ r, Finset (Slice f r)) : Finset α :=
  univ.filter fun a => (⟨a,rfl⟩ : Slice f (f a)) ∈ v (f a)

private theorem restrict_join {α I : Type*} [Fintype α] [DecidableEq I]
    (f : α → I) (v : ∀ r, Finset (Slice f r)) (r : I) :
    (join f v).subtype (fun a => f a = r) = v r := by
  ext ⟨a,ha⟩
  subst r
  simp [join]

private def splitEquiv {α I : Type*} [Fintype α] [Fintype I] [DecidableEq I]
    (f : α → I) (u : I → ℕ) :
    {B : Finset α // ∀ r, (B.filter (fun a => f a = r)).card = u r} ≃
      (∀ r, {s : Finset (Slice f r) // s.card = u r}) where
  toFun B r := ⟨B.val.subtype _, by simpa using B.property r⟩
  invFun v := ⟨join f (fun r => (v r).val), by
    intro r
    rw [←card_subtype, restrict_join]
    exact (v r).property⟩
  left_inv B := by
    apply Subtype.ext
    ext a
    simp [join]
  right_inv v := by
    funext r
    apply Subtype.ext
    exact restrict_join f _ r

theorem partition_count {α I : Type*} [Fintype α] [Fintype I] [DecidableEq I]
    (f : α → I) (u : I → ℕ) :
    Fintype.card {B : Finset α // ∀ r, (B.filter (fun a => f a = r)).card = u r} =
      ∏ r, Nat.choose (Fintype.card {a : α // f a = r}) (u r) := by
  rw [Fintype.card_congr (splitEquiv f u), Fintype.card_pi]
  simp [Slice]

/-- Each threshold subset with the prescribed chain counts is counted once.
The cut T is explicit and includes both endpoints. -/
theorem gap_threshold_subset_count {n h T : ℕ} (hh : 0<h) (u : Fin h → ℕ)
    (mass : ∑ r, u r = T) :
    Fintype.card {B : Finset (Fin n) // B.card = T ∧
      ∀ r : Fin h, chainLowerCount B h r.val = u r} =
      ∏ r : Fin h, Nat.choose (residuePrefixCount h r.val n) (u r) := by
  let f : Fin n → Fin h := fun a => ⟨a.val % h, Nat.mod_lt _ hh⟩
  have H (B : Finset (Fin n)) (r : Fin h) :
      (B.filter (fun a => f a = r)).card = chainLowerCount B h r.val := by
    simp [f,chainLowerCount,Fin.ext_iff]
  have E := Equiv.subtypeEquivRight (fun B : Finset (Fin n) =>
    (show (B.card = T ∧ ∀ r : Fin h, chainLowerCount B h r.val = u r) ↔
        (∀ r : Fin h, (B.filter (fun a => f a = r)).card = u r) from by
      simp only [H]
      constructor
      · exact And.right
      · intro v
        refine ⟨?_,v⟩
        calc
          B.card = ∑ r : Fin h, (B.filter (fun a => f a = r)).card :=
            card_eq_sum_card_fiberwise (t:=univ) (fun a _ => mem_univ (f a))
          _ = T := by simpa only [H,v] using mass))
  rw [Fintype.card_congr E]
  trans ∏ r, Nat.choose (Fintype.card {a : Fin n // f a = r}) (u r)
  · convert partition_count f u using 1
    exact congrArg (@Fintype.card _) (Subsingleton.elim _ _)
  apply prod_congr rfl
  intro r _
  congr 1
  rw [Fintype.card_subtype, ← chainPositions_card]
  simp [chainPositions,f,Fin.ext_iff]

private def bit {n : ℕ} (B : Finset (Fin n)) (i : Fin n) := decide (i ∈ B)

private theorem bit_card {n : ℕ} (B : Finset (Fin n)) (v : Bool) :
    Fintype.card {a : Fin n // bit B a = v} = if v then B.card else n-B.card := by
  cases v with
  | false =>
    simp only [bit,decide_eq_false_iff_not,Bool.false_eq_true,ite_false]
    rw [Fintype.card_subtype_compl]
    simp
  | true => simp [bit,Fintype.card_subtype]

/-- Exact number of rank placements giving a specified set at cut T. -/
theorem permutation_threshold_fiber {n T : ℕ} (B : Finset (Fin n)) (hB : B.card = T) :
    Fintype.card {p : RankPlacement n // thresholdSet p T = B} =
      T.factorial * (n-T).factorial := by
  let S := thresholdSet (Equiv.refl (Fin n)) T
  have hT : T≤n := by simpa [←hB] using B.card_le_univ
  have sSize : S.card = T := (thresholdSet_card _ T).trans (min_eq_right hT)
  have eqv : {p : RankPlacement n // thresholdSet p T = B} ≃ matchingEquiv (bit S) (bit B) :=
    Equiv.subtypeEquivRight (fun p => by
      constructor
      · intro eq a
        simp [bit,←eq,S,threshold_mem]
      · intro eq
        ext i
        have b := eq (p.symm i)
        simpa [bit,S,threshold_mem,iff_comm] using b)
  have sizes (v : Bool) : Fintype.card {a : Fin n // bit S a = v} =
      Fintype.card {a : Fin n // bit B a = v} := by rw [bit_card,bit_card,sSize,hB]
  rw [Fintype.card_congr eqv]
  convert (matchingEquiv_card (bit S) (bit B) sizes).trans
    (show (∏ v : Bool, (Fintype.card {a : Fin n // bit S a = v}).factorial) =
      T.factorial * (n-T).factorial from by simp [bit_card,sSize]) using 1
  exact congrArg (@Fintype.card _) (Subsingleton.elim _ _)

#print axioms gap_threshold_subset_count
#print axioms permutation_threshold_fiber

/-- Uniform rank permutations, before reading the input.  Multiplication by
the size of a single threshold fiber gives the exact numerator. -/
theorem gap_threshold_permutation_count {n h T : ℕ} (hh : 0<h) (hT : T≤n)
    (u : Fin h → ℕ) (mass : ∑ r, u r = T) :
    Fintype.card {p : RankPlacement n // ∀ r : Fin h,
      chainLowerCount (thresholdSet p T) h r.val = u r} =
      (∏ r : Fin h, Nat.choose (residuePrefixCount h r.val n) (u r)) *
      (T.factorial*(n-T).factorial) := by
  let E := {p : RankPlacement n // ∀ r : Fin h, chainLowerCount (thresholdSet p T) h r.val = u r}
  let V := {B : Finset (Fin n) // B.card = T ∧ ∀ r : Fin h, chainLowerCount B h r.val = u r}
  let cut : E → V := fun p =>
    ⟨thresholdSet p.val T,(thresholdSet_card _ _).trans (min_eq_right hT),p.property⟩
  have individual (B : V) : Fintype.card {p : E // cut p = B} = T.factorial*(n-T).factorial := by
    let equiv : {p : E // cut p = B} ≃ {p : RankPlacement n // thresholdSet p T = B.val} := {
      toFun := fun p => ⟨p.val.val,congrArg Subtype.val p.property⟩
      invFun := fun p => ⟨⟨p.val,by rw [p.property]; exact B.property.2⟩,Subtype.ext p.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    exact (Fintype.card_congr equiv).trans (permutation_threshold_fiber B.val B.property.1)
  have vcard : Fintype.card V = ∏ r : Fin h, Nat.choose (residuePrefixCount h r.val n) (u r) :=
    gap_threshold_subset_count hh u mass
  change Fintype.card E = _
  rw [← Fintype.card_congr (Equiv.sigmaFiberEquiv cut), Fintype.card_sigma]
  simp [individual,vcard]

#print axioms gap_threshold_permutation_count
end Shellsort.ThresholdOccupancyLaw
