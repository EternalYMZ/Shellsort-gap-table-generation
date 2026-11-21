import Shellsort.RoughGapScaleAssembly

/-! Complete deterministic error of a left-endpoint mesh on an actual rank placement.
The cut is *before* rank T, so the final cut has zero moment. -/
namespace Shellsort.RankMesh
open Finset RoughGapScaleAssembly
noncomputable section

def cut {n : ℕ} (p : RankPlacement n) (T : ℕ) : ℤ :=
  ∑ x : Fin n, if x.val < T then ((p x).val : ℤ) - x.val else 0

theorem cut_eq_thresholdMoment {n : ℕ} (p : RankPlacement n) (t : ℕ) :
    cut p (t+1) = thresholdMoment p t := by
  have perm := Equiv.sum_comp p (fun x : Fin n => if x.val ≤ t then (x.val : ℤ) else 0)
  simp only [cut, thresholdMoment, Nat.lt_succ_iff]
  simp_rw [mul_sub]
  rw [sum_sub_distrib]
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [perm]
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro x _
  split_ifs <;> simp

theorem cut_diff {n : ℕ} (p : RankPlacement n) (r : Fin n) :
    cut p (r.val+1) - cut p r.val = ((p r).val : ℤ) - r.val := by
  unfold cut
  rw [←sum_sub_distrib]
  have eqn (x : Fin n) :
      (if x.val < r.val+1 then ((p x).val : ℤ) - x.val else 0) -
      (if x.val < r.val then ((p x).val : ℤ) - x.val else 0) =
      if x = r then ((p r).val : ℤ) - r.val else 0 := by
    by_cases h : x=r
    · subst x; simp
    · have hh : x.val ≠ r.val := fun e => h (Fin.ext e)
      split_ifs <;> omega
  simp_rw [eqn]
  simp

theorem total_variation {n : ℕ} (p : RankPlacement n) :
    (∑ r : Fin n, (|cut p (r.val+1) - cut p r.val| : ℤ) : ℤ) = ∑ r : Fin n, |((p r).val : ℤ) - r.val| := by
  simp_rw [cut_diff]

private theorem telescoping (v : ℕ → ℤ) (a b : ℕ) (hab : a ≤ b) :
    |v b - v a| ≤ ∑ i ∈ Ico a b, |v (i+1) - v i| := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [sum_Ico_succ_top hab]
    exact (abs_sub_le _ _ _).trans (by linarith)

/-- Any left mesh whose points lie at most D slots behind, regular or not. -/
theorem mesh_error (v : ℕ → ℤ) (n D : ℕ) (left : ℕ → ℕ)
    (low : ∀ t < n, left t ≤ t) (span : ∀ t < n, t ≤ left t + D) :
    |(∑ t ∈ range n, v t) - (∑ t ∈ range n, v (left t))| ≤
      (D:ℤ) * ∑ i ∈ range n, |v (i+1)-v i| := by
  let f := fun i => |v (i+1)-v i|
  rw [←sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ t ∈ range n, ∑ i ∈ Ico (left t) t, f i := by
      exact sum_le_sum fun t ht => telescoping v _ _ (low t (mem_range.mp ht))
    _ = ∑ i ∈ range n, ∑ t ∈ range n, (if left t ≤ i ∧ i < t then f i else 0) := by
      rw [sum_comm]
      apply sum_congr rfl
      intro t ht
      rw [←sum_filter]
      congr 1
      ext i
      simp only [mem_Ico, mem_filter, mem_range]
      have := mem_range.mp ht
      omega
    _ ≤ ∑ i ∈ range n, (D:ℤ)* f i := by
      apply sum_le_sum
      intro i _
      rw [←sum_filter]
      simp only [sum_const, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      exact_mod_cast (show ((range n).filter fun t => left t ≤ i ∧ i < t).card ≤ D from by
        calc
          _ ≤ (Ioc i (i+D)).card := card_le_card (by
            intro t ht
            obtain ⟨h,a,b⟩ := mem_filter.mp ht
            have := span t (mem_range.mp h)
            exact mem_Ioc.mpr ⟨b, by omega⟩)
          _ = D := by simp)
    _ = _ := (mul_sum ..).symm

/-- The actual r-th shard representative is r-(r mod H).  The proof counts
each cut edge at most H-1 times and covers incomplete terminal shards. -/
theorem rank_mesh_error {n : ℕ} (p : RankPlacement n) (H : ℕ) (positive : 0<H) :
    |(∑ t ∈ range n, cut p t) - (∑ t ∈ range n, cut p (t - t % H))| ≤
      ((H-1 : ℕ) : ℤ) * ∑ r : Fin n, |((p r).val : ℤ)-r.val| := by
  have me := mesh_error (cut p) n (H-1) (fun t => t-t%H)
    (fun t _ => Nat.sub_le ..)
    (fun t _ => by have := Nat.mod_lt t positive; have := Nat.mod_le t H; omega)
  rw [←Fin.sum_univ_eq_sum_range (fun i => |cut p (i+1)-cut p i|)] at me
  rw [total_variation] at me
  exact me

/-- Same-interval sum of the "before rank" moments, checked against the
previous project definition of the true sum of squared displacements. -/
theorem cut_sum_square {n : ℕ} (p : RankPlacement n) :
    2*(∑ t ∈ range n, cut p t) = squareDisplacement p := by
  have end0 : cut p n = 0 := by
    unfold cut
    simp only [Fin.is_lt, ite_true, sum_sub_distrib]
    exact sub_eq_zero.mpr (Equiv.sum_comp p (fun i : Fin n => (i.val : ℤ)))
  have h0 : cut p 0 = 0 := by simp [cut]
  have ss (k : ℕ) :
      (∑ t ∈ range k, cut p (t+1)) - (∑ t ∈ range k, cut p t) =
      cut p k - cut p 0 := by
    induction k with
    | zero => simp
    | succ k ih =>
      simp only [sum_range_succ]
      linarith
  have A := ss n
  rw [end0, h0, sub_self, sub_eq_zero] at A
  rw [←A]
  simp_rw [cut_eq_thresholdMoment]
  exact twice_sum_thresholdMoment p

#print axioms cut_sum_square
#print axioms rank_mesh_error
#print axioms cut_eq_thresholdMoment
#print axioms cut_diff
#print axioms total_variation
#print axioms mesh_error
end
end Shellsort.RankMesh




