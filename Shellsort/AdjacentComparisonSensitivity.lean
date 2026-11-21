import Shellsort.AdjacentRankCost
import Shellsort.AdjacentCutLedger

/-! Stability of ordinary key *comparisons* (including stopping comparisons)
along an adjacent rank edit. -/
noncomputable section
namespace Shellsort.AdjacentComparisonSensitivity
open Finset

private def larger {n L : ℕ} (f : Fin L → Fin n) (j : Fin L) : Finset (Fin L) :=
  (Iio j).filter (fun i => f j < f i)

private def fee {n L : ℕ} (f : Fin L → Fin n) (j : Fin L) : ℕ :=
  min j.val ((larger f j).card + 1)

private theorem chain_fee {n L : ℕ} (f : Fin L → Fin n) :
    (insertionComparedExecution (List.ofFn f)).comparisons = ∑ j, fee f j := by
  classical
  have records := insertionComparedBack_records (List.ofFn f)
  have shifts := insertionComparedExecution_shifts (List.ofFn f)
  change (insertionComparedBack _).shifts = _ at shifts
  change (insertionComparedBack _).comparisons = _
  rw [shifts, insertionExecution_ofFn_count, AdjacentCutLedger.prefixMinima_ofFn,
    List.length_ofFn] at records
  have rewriteCounts (j : Fin L) :
      (∑ i : Fin L, if i < j ∧ f j < f i then 1 else 0) = (larger f j).card := by
    rw [Finset.sum_boole]
    apply congrArg Finset.card
    ext i
    simp [larger]
  simp_rw [rewriteCounts] at records
  have point (j : Fin L) :
      fee f j + (if ∀ i : Fin L, i < j → f j < f i then 1 else 0)
        = (larger f j).card + 1 := by
    unfold fee
    by_cases h : ∀ i : Fin L, i < j → f j < f i
    · have he : larger f j = Iio j := by ext i; simp [larger]; grind
      rw [if_pos h, he, Fin.card_Iio]
      omega
    · have hs : larger f j ⊂ Iio j := by
        apply Finset.ssubset_iff_of_subset (Finset.filter_subset ..) |>.mpr
        push Not at h
        obtain ⟨i, hi, hbad⟩ := h
        exact ⟨i, Finset.mem_Iio.mpr hi, fun h => (not_lt.mpr hbad) (Finset.mem_filter.mp h).2⟩
      have hlt := Finset.card_lt_card hs
      rw [Fin.card_Iio] at hlt
      simp [h, Nat.min_eq_right (show (larger f j).card + 1 ≤ j.val by omega)]
  have sum := Finset.sum_congr (s₁ := (univ : Finset (Fin L))) rfl (fun j _ => point j)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, Nat.mul_one] at sum
  omega

private theorem lost {n : ℕ} (a b x y : Fin n) (hab : b.val = a.val + 1)
    (hxy : x < y) (hbad : ¬Equiv.swap a b x < Equiv.swap a b y) : x = a ∧ y = b := by
  simp only [Equiv.swap_apply_def] at hbad
  split_ifs at hbad <;> simp_all only [Fin.lt_def, Fin.ext_iff] <;> first | trivial | omega

/-- On the single possibly affected insertion, the unit of movement variation
is absorbed by the omitted stop if the two ranks are the bottom two. -/
private theorem fee_edit {n L : ℕ} (f : Fin L → Fin n) (hf : Function.Injective f)
    (a b : Fin n) (hab : b.val = a.val + 1) (j : Fin L) (d : ℕ)
    (pay : ∀ i, i < j → f j = a → f i = b → a.val ≠ 0 → 1 ≤ d) :
    fee f j ≤ fee (fun i => Equiv.swap a b (f i)) j + d := by
  classical
  let g := fun i => Equiv.swap a b (f i)
  change fee f j ≤ fee g j + d
  by_cases hsub : larger f j ⊆ larger g j
  · have h := Finset.card_le_card hsub
    unfold fee
    omega
  · obtain ⟨i, hi, hl⟩ := Finset.not_subset.mp hsub
    have hi' := Finset.mem_filter.mp hi
    have hij := Finset.mem_Iio.mp hi'.1
    have bad : ¬ g j < g i := fun h => hl (Finset.mem_filter.mpr ⟨hi'.1,h⟩)
    obtain ⟨hja, hib⟩ := lost a b _ _ hab hi'.2 bad
    have inc : larger f j ⊆ insert i (larger g j) := by
      intro z hz
      by_cases hg : z ∈ larger g j
      · exact Finset.mem_insert_of_mem hg
      · obtain ⟨hzj, hr⟩ := Finset.mem_filter.mp hz
        have fail : ¬g j < g z := fun h => hg (Finset.mem_filter.mpr ⟨hzj,h⟩)
        have pair := lost a b _ _ hab hr fail
        exact Finset.mem_insert.mpr (.inl (hf (pair.2.trans hib.symm)))
    have hcard := (Finset.card_le_card inc).trans (Finset.card_insert_le ..)
    by_cases low : a.val = 0
    · have he : larger f j = Iio j := by
        ext z
        simp only [larger, mem_filter, mem_Iio, and_iff_left_iff_imp]
        intro hz
        have hne : f j ≠ f z := fun h => hz.ne (hf h).symm
        simp only [Fin.ext_iff, Fin.lt_def] at *
        omega
      rw [he,Fin.card_Iio] at hcard
      unfold fee
      omega
    · have hd := pay i hij hja hib low
      unfold fee
      omega

private def editCost {n : ℕ} (p : RankPlacement n) (a b : Fin n) (k : ℕ) : ℕ :=
  if (p a).val % k = (p b).val % k ∧ a.val ≠ 0 then 1 else 0

private theorem gap_edit {n : ℕ} (p : RankPlacement n) (a b : Fin n)
    (hab : b.val = a.val+1) (k : ℕ) (hk : 0<k) :
    gapComparisonCost p k hk ≤ gapComparisonCost (relabelSwap p a b) k hk + editCost p a b k := by
  classical
  let charge := fun x : Fin n => if p.symm x = a then editCost p a b k else 0
  have totalCharge : (∑ x : Fin n, charge x) = editCost p a b k := by
    rw [← Equiv.sum_comp p charge]
    simp [charge]
  rw [sum_positions_by_chains n k hk] at totalCharge
  unfold gapComparisonCost
  simp_rw [chain_fee]
  rw [←totalCharge, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro s _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  let slot := fun v : Fin (sourceTrialLength (n/k) (n%k) s.val) =>
    (positionChainEquiv n k hk).symm ⟨s,v⟩
  change fee (fun v => p.symm (slot v)) j ≤
    fee (fun v => Equiv.swap a b (p.symm (slot v))) j + charge (slot j)
  refine fee_edit _ ?_ a b hab _ _ ?_
  · intro x y he
    have ee := (positionChainEquiv n k hk).symm.injective (p.symm.injective he)
    exact eq_of_heq (Sigma.mk.inj ee).2
  · intro i _ hj hi low
    have ja : p a = slot j := by rw [←hj]; simp
    have ib : p b = slot i := by rw [←hi]; simp
    have hm : (p a).val % k = (p b).val % k := by
      rw [ja,ib]
      exact (positionChainEquiv_symm_residue n k hk ⟨s,j⟩).trans
        (positionChainEquiv_symm_residue n k hk ⟨s,i⟩).symm
    simp [charge,hj,editCost,hm,low]

/-- Directed bound on the actual comparison fee; any positive word is allowed. -/
theorem word_edit_le {n : ℕ} (p : RankPlacement n) (a b : Fin n)
    (hab : b.val = a.val+1) (w : List {k : ℕ // 0<k}) :
    ordinaryWordComparisons p w ≤ ordinaryWordComparisons (relabelSwap p a b) w +
      (if a.val=0 then 0 else 1) := by
  induction w generalizing p with
  | nil => simp [ordinaryWordComparisons]
  | cons h t ih =>
    have H := gap_edit p a b hab h.val h.property
    simp only [ordinaryWordComparisons]
    by_cases meet : (p a).val % h.val = (p b).val % h.val
    · rw [adj_gapSort_of_meet p a b h.val meet]
      by_cases low : a.val=0 <;> simp [editCost,meet,low] at * <;> omega
    · rw [adj_gapSort_of_separate p a b hab h.val meet]
      have tail := ih (gapSort p h.val)
      simp only [editCost,meet,false_and,ite_false,Nat.add_zero] at H
      omega

theorem word_adjacent_comparisons {n : ℕ} (p : RankPlacement n) (a b : Fin n)
    (hab : b.val = a.val+1) (w : List {k : ℕ // 0<k}) :
    Nat.dist (ordinaryWordComparisons p w) (ordinaryWordComparisons (relabelSwap p a b) w) ≤
      (if a.val=0 then 0 else 1) := by
  have h := word_edit_le p a b hab w
  have r := word_edit_le (relabelSwap p a b) a b hab w
  rw [relabelSwap_twice] at r
  unfold Nat.dist
  omega

#print axioms word_adjacent_comparisons
end Shellsort.AdjacentComparisonSensitivity
