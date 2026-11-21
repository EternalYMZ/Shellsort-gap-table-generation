import Shellsort.TagThreshold
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-! Finite kernel identities for averaging the threshold-count profile. -/
noncomputable section
namespace Shellsort

open scoped BigOperators

/-- The squared length of a translated unit-mass kernel after subtracting
its mean. Translation may be any permutation of the finite index type. -/
theorem shifted_kernel_energy {α : Type*} [Fintype α] [Nonempty α]
    (e : Equiv.Perm α) (μ : α → ℝ) (hmass : ∑ i, μ i = 1) :
    ∑ i, (μ (e i) - (Fintype.card α : ℝ)⁻¹)^2 =
      (∑ i, (μ i)^2) - (Fintype.card α : ℝ)⁻¹ := by
  classical
  rw [Equiv.sum_comp e (fun i => (μ i - (Fintype.card α : ℝ)⁻¹)^2)]
  have hk : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  calc
    ∑ i, (μ i - (Fintype.card α : ℝ)⁻¹)^2 =
        ∑ i, ((μ i)^2 - (2 * (Fintype.card α : ℝ)⁻¹) * μ i +
          (Fintype.card α : ℝ)⁻¹ ^ 2) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        hmass, mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp
      ring

/-- Smoothing uniformly on a nonempty window of width B.card. -/
theorem uniform_window_shifted_energy {α : Type*} [Fintype α] [Nonempty α]
    [DecidableEq α] (e : Equiv.Perm α) (B : Finset α) (hne : B.Nonempty) :
    ∑ i, ((if e i ∈ B then (B.card : ℝ)⁻¹ else 0) -
          (Fintype.card α : ℝ)⁻¹)^2 =
        (B.card : ℝ)⁻¹ - (Fintype.card α : ℝ)⁻¹ := by
  have hw : (B.card : ℝ) ≠ 0 := by exact_mod_cast hne.card_pos.ne'
  have hm : (∑ i : α, if i ∈ B then (B.card : ℝ)⁻¹ else 0) = 1 := by
    simp [hw]
  rw [shifted_kernel_energy e (fun i => if i ∈ B then (B.card : ℝ)⁻¹ else 0) hm]
  simp_rw [ite_pow, zero_pow (by decide : 2 ≠ 0)]
  simp
  field_simp

/-- A low slot contributes a translated copy of the kernel, centered by its
mean. For residues, slotShift sends each slot to its cyclic translation. -/
def centeredKernelCount {α : Type*} [Fintype α] {n : ℕ}
    (slotShift : Fin n → Equiv.Perm α) (μ : α → ℝ) (low : Finset (Fin n))
    (r : α) : ℝ :=
  ∑ i ∈ low, (μ (slotShift i r) - (Fintype.card α : ℝ)⁻¹)

/-- Flipping the label of one true key through the fixed sorting word
changes the smoothed count by the kernel placed at its actual final slot. -/
theorem centeredKernelCount_word_toggle {α : Type*} [Fintype α] {n : ℕ}
    (slotShift : Fin n → Equiv.Perm α) (μ : α → ℝ) (p : RankPlacement n)
    (x : Fin n) (ks : List ℕ) (r : α) :
    centeredKernelCount slotShift μ
        (lowerWord (insert (p x) (thresholdSet p x.val)) ks) r -
      centeredKernelCount slotShift μ (lowerWord (thresholdSet p x.val) ks) r =
        μ (slotShift (sortWord p ks x) r) - (Fintype.card α : ℝ)⁻¹ := by
  rw [← thresholdSet_succ_tag, ← sortWord_threshold_commutes,
    ← sortWord_threshold_commutes, thresholdSet_succ_tag]
  simp only [centeredKernelCount, Finset.sum_insert (tag_not_in_threshold _ _),
    add_sub_cancel_right]

/-- Exact energy of the real sorting word's one-label derivative for
an arbitrary nonempty uniform window. -/
theorem uniform_kernel_word_toggle_energy {α : Type*} [Fintype α] [Nonempty α]
    [DecidableEq α] {n : ℕ} (slotShift : Fin n → Equiv.Perm α)
    (B : Finset α) (hne : B.Nonempty) (p : RankPlacement n) (x : Fin n) (ks : List ℕ) :
    let μ : α → ℝ := fun i => if i ∈ B then (B.card : ℝ)⁻¹ else 0
    ∑ r, (centeredKernelCount slotShift μ
          (lowerWord (insert (p x) (thresholdSet p x.val)) ks) r -
        centeredKernelCount slotShift μ (lowerWord (thresholdSet p x.val) ks) r)^2 =
      (B.card : ℝ)⁻¹ - (Fintype.card α : ℝ)⁻¹ := by
  dsimp only
  simp_rw [centeredKernelCount_word_toggle]
  exact uniform_window_shifted_energy (slotShift (sortWord p ks x)) B hne

end Shellsort
end
