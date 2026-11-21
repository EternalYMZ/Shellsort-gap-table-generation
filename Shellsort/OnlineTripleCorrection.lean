import Shellsort.OnlineTripleGaps

/-! A uniform bound for the least correction in the seed-(1,4) recurrence.
For each positive gcd up to 194, check every residue once. If the old gcd
has a factor 2 or 5, the new gcd is a proper divisor of the scaled error. -/

namespace Shellsort.OnlineTriple

private def width (d : ℕ) : ℕ := if 2 ∣ d ∨ 5 ∣ d then 6 else 3

-- The outer index 0 has no residues. Kernel reduction checks the table.
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem small_cover :
    ∀ d : Fin 195, ∀ r : Fin d.val,
      ∃ i : Fin (width d.val), d.val.Coprime (r.val + i.val) := by decide +kernel

private theorem periodic_cover {d : ℕ} (hd : 0 < d) (hu : d ≤ 194) (t : ℕ) :
    ∃ i < width d, d.Coprime (t + i) := by
  obtain ⟨i, hi⟩ := small_cover ⟨d, by omega⟩ ⟨t % d, Nat.mod_lt _ hd⟩
  refine ⟨i.val, i.isLt, ?_⟩
  have heq := Nat.mod_add_div t d
  have hrewrite : t+i.val = (t % d + i.val) + d*(t/d) := by omega
  rw [hrewrite, Nat.coprime_add_mul_left_right]
  exact hi

private theorem proper_divisor_bound {a e : ℕ} (he : 0 < e) (hdiv : a ∣ e)
    (hne : a ≠ e) : 2*a ≤ e := by
  obtain ⟨q, hq⟩ := hdiv
  have htwo : 2 ≤ q := by
    by_contra! h
    have : q = 0 ∨ q = 1 := by omega
    rcases this with h | h <;> simp_all
  simpa [hq, Nat.mul_comm] using Nat.mul_le_mul_left a htwo

private theorem gcd_ne_error {d y z p : ℕ} (hdy : d ∣ y) (hcop : d.Coprime z)
    (hp : 1 < p) (hpd : p ∣ d) (hp50 : p ∣ 50) :
    y.gcd z ≠ 50*z-107*y := by
  intro heq
  have hpe : p ∣ 50*z-107*y := Nat.dvd_sub
    (Nat.dvd_mul_right_of_dvd hp50 z)
    (Nat.dvd_mul_left_of_dvd (Nat.dvd_trans hpd hdy) 107)
  rw [← heq] at hpe
  have hpz := Nat.dvd_trans hpe (Nat.gcd_dvd_right y z)
  have hp1 := Nat.dvd_gcd hpd hpz
  rw [show d.gcd z = 1 from hcop] at hp1
  have := Nat.le_of_dvd Nat.one_pos hp1
  omega

/-- One step preserves the gcd bound and corrects the proposal by at most five. -/
theorem correction_step (x y : ℕ) (hpos : 0 < x.gcd y) (hu : x.gcd y ≤ 194) :
    next x y ≤ Actual214.nextGap y + 5 ∧ y.gcd (next x y) ≤ 194 := by
  let d := x.gcd y
  let t := Actual214.nextGap y
  let z := next x y
  obtain ⟨i, hi, hcop⟩ := periodic_cover hpos hu t
  have hz : z ≤ t+i := next_min (Nat.le_add_right t i) hcop
  have hspec : t ≤ z ∧ d.Coprime z := next_spec x y
  obtain ⟨hl, hh⟩ := Actual214.scaled_next_bounds y
  change 107*y+45 ≤ 50*t at hl
  change 50*t ≤ 107*y+94 at hh
  have he : 0 < 50*z-107*y := by omega
  have hdiv : y.gcd z ∣ 50*z-107*y := Nat.dvd_sub
    (Nat.dvd_mul_left_of_dvd (Nat.gcd_dvd_right y z) 50)
    (Nat.dvd_mul_left_of_dvd (Nat.gcd_dvd_left y z) 107)
  change i < width d at hi
  change z ≤ t+5 ∧ y.gcd z ≤ 194
  by_cases h : 2 ∣ d ∨ 5 ∣ d
  · simp only [width, ite_eq_left h] at hi
    have hne : y.gcd z ≠ 50*z-107*y := by
      rcases h with h | h
      · exact gcd_ne_error (Nat.gcd_dvd_right x y) hspec.2 (by decide : 1 < 2) h (by decide)
      · exact gcd_ne_error (Nat.gcd_dvd_right x y) hspec.2 (by decide : 1 < 5) h (by decide)
    have := proper_divisor_bound he hdiv hne
    omega
  · simp only [width, ite_eq_right h] at hi
    have := Nat.le_of_dvd he hdiv
    omega

/-- Every adjacent gcd of the generated gaps is at most 194. -/
theorem adjacent_gcd_le_194 (j : ℕ) : (gap j).gcd (gap (j+1)) ≤ 194 := by
  induction j with
  | zero => decide
  | succ j ih =>
    have hp : 0 < gap (j+1) := by have := gap_strict j; omega
    rw [gap_rec]
    exact (correction_step _ _ (Nat.gcd_pos_of_pos_right _ hp) ih).2

/-- At every index the ordinary proposal and the actual gap differ by at most five. -/
theorem uniform_correction_le_five (j : ℕ) :
    gap (j+2) - Actual214.nextGap (gap (j+1)) ≤ 5 := by
  have hp : 0 < gap (j+1) := by have := gap_strict j; omega
  have h := (correction_step _ _ (Nat.gcd_pos_of_pos_right _ hp) (adjacent_gcd_le_194 j)).1
  rw [gap_rec]
  omega

/-- Uniform scaled-error bounds include the seed edge (1,4). -/
theorem scaled_gap_bounds (j : ℕ) :
    107 * gap j + 45 ≤ 50 * gap (j+1) ∧
    50 * gap (j+1) ≤ 107 * gap j + 344 := by
  cases j with
  | zero => decide
  | succ j =>
    change 107 * gap (j+1) + 45 ≤ 50 * gap (j+2) ∧
      50 * gap (j+2) ≤ 107 * gap (j+1) + 344
    obtain ⟨hl, hu⟩ := Actual214.scaled_next_bounds (gap (j+1))
    have hnext := (next_spec (gap j) (gap (j+1))).1
    rw [← gap_rec j] at hnext
    have hc := uniform_correction_le_five j
    omega

end Shellsort.OnlineTriple
