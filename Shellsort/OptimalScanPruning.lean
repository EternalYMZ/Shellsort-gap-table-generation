import Shellsort.PredeterminedOptimum

/-! A certificate for exact search over the legal, predetermined gap tables. -/
noncomputable section
namespace Shellsort.PredeterminedOptimum
open HarvestBlockIteration

/-- Each noninitial slot of each gap chain incurs at least one key comparison. -/
def scanFloor (n : ℕ) (w : PositiveWord) : ℕ :=
  (w.map fun h => n - h.val).sum

theorem scanFloor_le_mean (n : ℕ) (w : PositiveWord) :
    (scanFloor n w : ℝ) ≤ mean n w := by
  rw [← uniformAverage_const n (scanFloor n w : ℝ)]
  apply uniformAverage_mono
  intro p
  exact_mod_cast (max_le_iff.mp (ordinaryWord_scan_bounds p w).1).2

/-- Once the best searched mean is at most the budget, a table outside the
    budget has a strictly greater mean. Equality at the boundary is retained. -/
theorem outside_scan_budget {n B : ℕ} {w v : PositiveWord}
    (hw : mean n w ≤ (B : ℝ)) (hv : B < scanFloor n v) :
    mean n w < mean n v := by
  exact (hw.trans_lt (by exact_mod_cast hv)).trans_le (scanFloor_le_mean n v)

theorem exact_minimum_of_scan_budget {n B : ℕ} {w : PositiveWord}
    (hw : Legal n w) (hcost : mean n w ≤ (B : ℝ))
    (hbest : ∀ v, Legal n v → scanFloor n v ≤ B → mean n w ≤ mean n v) :
    Legal n w ∧ ∀ v, Legal n v → mean n w ≤ mean n v := by
  refine ⟨hw, fun v hv => ?_⟩
  by_cases h : scanFloor n v ≤ B
  · exact hbest v hv h
  · exact (outside_scan_budget hcost (lt_of_not_ge h)).le

#print axioms exact_minimum_of_scan_budget
end Shellsort.PredeterminedOptimum
