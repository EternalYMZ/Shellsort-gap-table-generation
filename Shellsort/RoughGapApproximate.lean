import Shellsort.RoughGapCanonical

/-! Selection with an absolute error in the paper's U = Q/(2n) units.
The existence of a sufficiently accurate score and the arithmetic contraction
of the actual menu are separate premises, not asserted here. -/
namespace Shellsort.RoughGapApproximate
open Finset RoughGapCanonical

/-- Paper score: meanEnergy in the canonical module uses Q/n, hence divide by two. -/
noncomputable def meanU {n : ℕ} (P : RankPlacement n → RankPlacement n) (h : ℕ) : ℝ :=
  meanEnergy P h / 2

/-- Selection regret even with correlated or deterministic errors. -/
theorem regret {G : Finset ℕ} {q est : ℕ → ℝ} {s j : ℕ} {e : ℝ}
    (hs : s ∈ G) (hj : j ∈ G) (approx : ∀ i ∈ G, |est i - q i| ≤ e)
    (best : ∀ i ∈ G, est s ≤ est i) :
    q s ≤ q j + 2*e := by
  have low := (abs_le.mp (approx s hs)).1
  have high := (abs_le.mp (approx j hj)).2
  linarith [best j hj]

/-- Actual expected U of the approximate minimizer versus the exact menu average. -/
theorem meanU_le_menu_add {n : ℕ} (P : RankPlacement n → RankPlacement n)
    (G : Finset ℕ) (ne : G.Nonempty) {est : ℕ → ℝ} {s : ℕ} {e : ℝ}
    (hs : s ∈ G) (approx : ∀ i ∈ G, |est i - meanU P i| ≤ e)
    (best : ∀ i ∈ G, est s ≤ est i) :
    meanU P s ≤ (∑ i ∈ G, meanU P i) / G.card + 2*e := by
  have hb := regret hs (pick_spec P G ne).1 approx best
  have hc := pick_le_menu_mean P G ne
  unfold meanU at *
  rw [← sum_div]
  linarith [show (∑ i ∈ G, meanEnergy P i) / 2 / G.card =
      (∑ i ∈ G, meanEnergy P i) / G.card / 2 by ring]

/-- Scale induction with tolerated score regret d H_next². -/
theorem invariant (levels : ℕ) (q H : ℕ → ℝ) (a k d A B : ℝ)
    (ha : 0 ≤ a) (hk : 0 ≤ k) (hA : 0 ≤ A)
    (budget : a*(A*B)^2 + k*(A*B) + d ≤ A^2)
    (positive : ∀ i ≤ levels, 0 ≤ H i)
    (initial : q 0 ≤ (A * H 0)^2)
    (ratio : ∀ i < levels, H i ≤ B * H (i+1))
    (step : ∀ i < levels, q (i+1) ≤ a*q i + k*H (i+1)*Real.sqrt (q i) + d*(H (i+1))^2) :
    ∀ i ≤ levels, q i ≤ (A * H i)^2 := by
  intro i hi
  induction i with
  | zero => exact initial
  | succ i ih =>
    have il : i < levels := by omega
    have H0 := positive i il.le
    have H1 := positive (i+1) hi
    have old := ih il.le
    have compare : A * H i ≤ (A*B) * H (i+1) := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (ratio i il) hA
    have sq := pow_le_pow_left₀ (mul_nonneg hA H0) compare 2
    have root : Real.sqrt (q i) ≤ A * H i := by
      simpa only [Real.sqrt_sq (mul_nonneg hA H0)] using Real.sqrt_le_sqrt old
    calc
      q (i+1) ≤ _ := step i il
      _ ≤ a*((A*B)*H (i+1))^2 + k*H (i+1)*((A*B)*H (i+1)) + d*(H (i+1))^2 :=
        add_le_add_left (add_le_add (mul_le_mul_of_nonneg_left (old.trans sq) ha)
          (mul_le_mul_of_nonneg_left (root.trans compare) (mul_nonneg hk H1))) _
      _ = (a*(A*B)^2+k*(A*B)+d)*(H (i+1))^2 := by ring
      _ ≤ A^2*(H (i+1))^2 := mul_le_mul_of_nonneg_right budget (sq_nonneg _)
      _ = _ := by ring

/-- Explicitly sufficient slack: choose A≥1 and A≥(kB+d)/(1−aB²).
The constants do not depend on the scale count. -/
theorem budget_of_slack {a k d A B : ℝ} (hd : 0 ≤ d) (hA : 1 ≤ A)
    (hr : a*B^2 < 1) (hm : (k*B+d)/(1-a*B^2) ≤ A) :
    a*(A*B)^2+k*(A*B)+d ≤ A^2 := by
  have hs : k*B+d ≤ A*(1-a*B^2) := (div_le_iff₀ (by linarith)).mp hm
  have p := mul_le_mul_of_nonneg_right hs (show 0 ≤ A by linarith)
  have t := mul_le_mul_of_nonneg_left hA hd
  nlinarith only [p,t]

/-- A posteriori, asymmetrical certificate. To inherit `menu mean + r` one
need not order all the candidates: an upper bound for this candidate and a
lower bound on the menu average suffice. -/
theorem interval_certificate {n : ℕ} (P : RankPlacement n → RankPlacement n)
    (G : Finset ℕ) (lo : ℕ → ℝ) (s : ℕ) (upper r : ℝ)
    (hs : meanU P s ≤ upper) (hl : ∀ i ∈ G, lo i ≤ meanU P i)
    (cert : upper ≤ (∑ i ∈ G, lo i) / G.card + r) :
    meanU P s ≤ (∑ i ∈ G, meanU P i) / G.card + r := by
  have lower := sum_le_sum hl
  exact hs.trans (cert.trans (by gcongr))

#print axioms interval_certificate
#print axioms regret
#print axioms meanU_le_menu_add
#print axioms invariant
#print axioms budget_of_slack
end Shellsort.RoughGapApproximate


