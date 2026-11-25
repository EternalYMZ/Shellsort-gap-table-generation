import Shellsort.ActualMenuMoment

/-! A sharper order dependence for the P09 conditional moment argument.
The input is the averaged adjacent-order drift. The moment array may come
from any law with the stated Cauchy–Schwarz and initial bounds. -/

namespace Shellsort.AdjacentMomentEnvelope

/-- The bound at order `q`, used for `q ≥ 2`. -/
noncomputable def envelope (q : ℕ) : ℝ :=
  (4 / 3 : ℝ)^q * 2^(65*q*(q+1)+130)

private theorem envelope_succ (q : ℕ) :
    envelope (q+1) = (4/3 : ℝ) * (2:ℝ)^(130*(q+1)) * envelope q := by
  have exp : 65*(q+1)*(q+1+1)+130 = 130*(q+1)+(65*q*(q+1)+130) := by ring
  unfold envelope
  rw [exp, pow_add (2:ℝ), pow_succ (4/3:ℝ)]
  ring

private theorem one_le_envelope (q : ℕ) : 1 ≤ envelope q :=
  one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by norm_num))

set_option exponentiation.threshold 520 in
/-- For an array of averaged moments, Cauchy–Schwarz at order one and the
averaged one-step drift imply a bound uniform in prefix length. -/
theorem all_prefixes (m : ℕ → ℕ → ℝ)
    (initial : ∀ q, 2 ≤ q → m 0 q ≤ 1)
    (cauchy : ∀ k, (m k 1)^2 ≤ m k 2)
    (drift : ∀ k q, 2 ≤ q →
      m (k+1) q ≤ m k q / 4 + (2:ℝ)^(130*q) * m k (q-1)) :
    ∀ q, 2 ≤ q → ∀ k, m k q ≤ envelope q := by
  let K : ℝ := (4/3) * 2^260
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have base : envelope 2 = K^2 := by
    change (4/3:ℝ)^2 * 2^520 = ((4/3:ℝ)*2^260)^2
    rw [mul_pow, ← pow_mul]
  have orderTwo : ∀ k, m k 2 ≤ envelope 2 := by
    intro k
    induction k with
    | zero => exact (initial 2 (by decide)).trans (one_le_envelope 2)
    | succ k ih =>
      rw [base] at ih ⊢
      have h1 : m k 1 ≤ K := by
        have habs := (sq_le_sq.mp ((cauchy k).trans ih))
        exact (le_abs_self _).trans (by simpa [abs_of_nonneg hK] using habs)
      calc
        m (k+1) 2 ≤ m k 2 / 4 + (2:ℝ)^260 * m k 1 := drift k 2 (by decide)
        _ ≤ K^2 / 4 + (2:ℝ)^260 * K := by gcongr
        _ = K^2 := by dsimp [K]; ring
  intro q hq
  induction q, hq using Nat.le_induction with
  | base => exact orderTwo
  | succ q hq prev =>
    intro k
    induction k with
    | zero => exact (initial (q+1) (by omega)).trans (one_le_envelope _)
    | succ k ih =>
      calc
        m (k+1) (q+1) ≤ m k (q+1)/4 + (2:ℝ)^(130*(q+1)) * m k q := by
          simpa using drift k (q+1) (by omega)
        _ ≤ envelope (q+1)/4 + (2:ℝ)^(130*(q+1)) * envelope q := by
          gcongr
          exact prev k
        _ = envelope (q+1) := by rw [envelope_succ]; ring

#print axioms all_prefixes
end Shellsort.AdjacentMomentEnvelope
