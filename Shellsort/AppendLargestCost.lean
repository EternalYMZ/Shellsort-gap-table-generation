import Shellsort.AdjacentCutLedger
import Shellsort.AdjacentRankCost

/-! Appending a new largest key at the right endpoint commutes with the
actual gap transitions and charges one extra stopping comparison for each
nontrivial child pass. -/
noncomputable section
namespace Shellsort.AppendLargestCost
open Finset
open scoped Classical

@[simp] private theorem last_not_lt_cast {n} (z : Fin n) : ¬ Fin.last n < z.castSucc :=
  not_lt_of_ge (Fin.le_last _)

private def extendFun {n : ℕ} (f : Fin n → Fin n) : Fin (n+1) → Fin (n+1) :=
  Fin.lastCases (Fin.last n) (fun x => (f x).castSucc)

def extend {n : ℕ} (p : RankPlacement n) : RankPlacement (n+1) where
  toFun := extendFun p
  invFun := extendFun p.symm
  left_inv x := by
    refine Fin.lastCases ?_ (fun i => ?_) x <;> simp [extendFun]
  right_inv x := by
    refine Fin.lastCases ?_ (fun i => ?_) x <;> simp [extendFun]

@[simp] theorem extend_last {n} (p : RankPlacement n) :
    extend p (Fin.last n) = Fin.last n := by simp [extend,extendFun]
@[simp] theorem extend_old {n} (p : RankPlacement n) (i : Fin n) :
    extend p i.castSucc = (p i).castSucc := by simp [extend,extendFun]
@[simp] theorem inv_last {n} (p : RankPlacement n) :
    (extend p).symm (Fin.last n) = Fin.last n := by simp [extend,extendFun]
@[simp] theorem inv_old {n} (p : RankPlacement n) (i : Fin n) :
    (extend p).symm i.castSucc = (p.symm i).castSucc := by simp [extend,extendFun]

theorem extend_sort {n} (p : RankPlacement n) (k : ℕ) :
    gapSort (extend p) k = extend (gapSort p k) := by
  apply gapSort_unique
  · intro x
    refine Fin.lastCases ?_ (fun i => ?_) x
    · simp
    · simpa using gapSort_preserves_residue p k i
  · intro x y
    refine Fin.lastCases ?_ (fun i => ?_) x <;> refine Fin.lastCases ?_ (fun j => ?_) y
    · simp
    · simp
    · simp
    · intro h
      simp only [extend_old, Fin.castSucc_lt_castSucc_iff]
      exact gapSort_sorted p k i j (by simpa [gapSort_preserves_residue] using h)

private theorem extend_inversions {n} (p : RankPlacement n) (k : ℕ) :
    gapInversions (extend p) k = gapInversions p k := by
  simp only [gapInversions_nat_pair_sum]
  rw [Fin.sum_univ_castSucc]
  simp_rw [Fin.sum_univ_castSucc]
  simp

private def recordAt {n} (p : RankPlacement n) (k : ℕ) (j : Fin n) : Prop :=
  ∀ i : Fin n, i<j → i.val % k = j.val % k → p.symm j < p.symm i

private theorem count_records {n} (p : RankPlacement n) (k : ℕ) (hk : 0<k) :
    gapPrefixMinima p k hk =
      ∑ j : Fin n, if recordAt p k j then 1 else 0 := by
  classical
  rw [gapPrefixMinima,sum_positions_by_chains n k hk]
  apply sum_congr rfl
  intro s _
  rw [AdjacentCutLedger.prefixMinima_ofFn]
  apply sum_congr rfl
  intro j _
  apply if_congr _ rfl rfl
  constructor
  · intro h i hi hm
    obtain ⟨⟨s',v⟩,rfl⟩ := (positionChainEquiv n k hk).symm.surjective i
    simp only [positionChainEquiv_symm_residue] at hm
    obtain rfl := Fin.ext hm
    exact h v ((chainPosition_lt_iff ..).mp hi)
  · intro h i hi
    apply h
    · exact (chainPosition_lt_iff ..).mpr hi
    · simp [positionChainEquiv_symm_residue]

private theorem record_old {n} (p : RankPlacement n) (k : ℕ) (j : Fin n) :
    recordAt (extend p) k j.castSucc ↔ recordAt p k j := by
  constructor
  · intro h i hi hm
    simpa using h i.castSucc (by simpa using hi) hm
  · intro h i
    refine Fin.lastCases ?_ (fun z => ?_) i
    · simp
    · intro hz hm
      simpa using h z (by simpa using hz) hm

private theorem no_record_last {n} (p : RankPlacement n) (k : ℕ) (hk : 0<k) (hkn : k≤n) :
    ¬ recordAt (extend p) k (Fin.last n) := by
  intro h
  let z : Fin n := ⟨n-k, by omega⟩
  have hm : z.val % k = n%k := by
    have t : n=(n-k)+k := by omega
    conv_rhs => rw [t,Nat.add_mod_right]
  have bad := h z.castSucc (Fin.castSucc_lt_last z) hm
  simp at bad

theorem extend_gap_comparisons {n} (p : RankPlacement n) (k : ℕ)
    (hk : 0<k) (hkn : k≤n) :
    gapComparisonCost (extend p) k hk = gapComparisonCost p k hk + 1 := by
  classical
  have father := gapComparisonCost_records p k hk
  have child := gapComparisonCost_records (extend p) k hk
  have recordEq : gapPrefixMinima (extend p) k hk = gapPrefixMinima p k hk := by
    rw [count_records,count_records,Fin.sum_univ_castSucc]
    simp [record_old,no_record_last p k hk hkn]
  rw [recordEq,gapInsertionCost_eq_gapInversions, extend_inversions] at child
  rw [gapInsertionCost_eq_gapInversions] at father
  omega

/-- Pointwise comparison identity for the ordinary executed word. A gap equal
to the parent length is counted: it is empty in the parent execution. -/
theorem extend_word_comparisons {n} (p : RankPlacement n) (w : List {k : ℕ // 0<k})
    (hw : ∀ h ∈ w, h.val ≤ n) :
    ordinaryWordComparisons (extend p) w = ordinaryWordComparisons p w + w.length := by
  induction w generalizing p with
  | nil => simp [ordinaryWordComparisons]
  | cons k ks ih =>
    have hc := extend_gap_comparisons p k.val k.property (hw k (List.mem_cons_self ..))
    have hp := ih (gapSort p k.val) (fun h hh => hw h (List.mem_cons_of_mem _ hh))
    simp only [ordinaryWordComparisons,extend_sort,List.length_cons,hp,hc]
    omega

#print axioms extend_word_comparisons
end Shellsort.AppendLargestCost
