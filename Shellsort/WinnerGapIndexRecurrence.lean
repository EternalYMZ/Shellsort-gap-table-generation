import Mathlib.Tactic

/-! Solving the scalar log-gap recurrence. Index zero denotes the first gap.
    The Shellsort prefix comparison giving the recurrence is a separate result. -/
namespace Shellsort.WinnerGapIndexRecurrence

theorem explicit_bound (a : ℕ → ℝ)
    (step : ∀ j : ℕ, a j ≤ 20 + 3*(j:ℝ) + 4*∑ i ∈ Finset.range j, a i) (j : ℕ) :
    4*a j + 3 ≤ 83*(5:ℝ)^j := by
  have envelope (t : ℕ) : 4*(20 + 3*(t:ℝ) + 4*∑ i ∈ Finset.range t, a i) + 3
      ≤ 83*(5:ℝ)^t := by
    induction t with
    | zero => norm_num
    | succ t ih =>
      rw [Finset.sum_range_succ, Nat.cast_succ, pow_succ]
      linarith [step t]
  linarith [step j, envelope j]

#print axioms explicit_bound
end Shellsort.WinnerGapIndexRecurrence
