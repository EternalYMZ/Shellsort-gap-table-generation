import Shellsort.HarvestBlockIteration

/-! A genuine minimum-score choice after an arbitrary preprocessing map,
with a varying bound on mean square displacement. -/
noncomputable section
namespace Shellsort.CanonicalWarmStart
open Actual214 HarvestScaleNumbers HarvestMenuBlock HarvestBlockIteration Finset

def score {n : ℕ} (P : RankPlacement n → RankPlacement n) (j h : ℕ) : ℝ :=
  meanEnergy (fun p => block j h (P p))

/-- Every tie in the exact score is allowed.  The ambient input size `n`
and the preceding scale `u` are separate parameters. -/
theorem minimizing_block_step {n : ℕ} (hn : 0<n) (P : RankPlacement n → RankPlacement n)
    (j u : ℕ) (large : 9400 ≤ gap j) (ratio : u ≤ 2^16 * gap j)
    (Z : ℝ) (zpos : 0 ≤ Z) (initial : meanEnergy P ≤ ((u:ℝ)*Z)^2)
    (h : ℕ) (minimal : ∀ v ∈ choices j, score P j h ≤ score P j v) (suffix : List ℕ) :
    meanEnergy (fun p => sortWord (block j h (P p)) suffix) ≤
      ((gap j:ℝ)*(Z/2+(2:ℝ)^114))^2 := by
  obtain ⟨v,memv,good⟩ := select_actual_linear_block hn P j large
  change score P j v ≤ (1/(2:ℝ)^47)*meanEnergy P +
    (2:ℝ)^98*(gap j:ℝ)*Real.sqrt (meanEnergy P) at good
  have r : (u:ℝ) ≤ (2:ℝ)^16*(gap j:ℝ) := by exact_mod_cast ratio
  have cap : meanEnergy P ≤ (((2:ℝ)^16*(gap j:ℝ))*Z)^2 :=
    initial.trans (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right r zpos) 2)
  have rootCap := (Real.sqrt_le_sqrt cap).trans_eq (Real.sqrt_sq (by positivity))
  have numeric : (1/(2:ℝ)^15)*Z^2 + (2:ℝ)^114*Z ≤ (Z/2+(2:ℝ)^114)^2 := by
    nlinarith only [sq_nonneg Z]
  calc
    _ ≤ score P j h := word_mean_le (fun p => block j h (P p)) suffix
    _ ≤ score P j v := minimal v memv
    _ ≤ _ := good
    _ ≤ (1/(2:ℝ)^47)*(((2:ℝ)^16*(gap j:ℝ))*Z)^2 +
        (2:ℝ)^98*(gap j:ℝ)*(((2:ℝ)^16*(gap j:ℝ))*Z) := by gcongr
    _ = (gap j:ℝ)^2*((1/(2:ℝ)^15)*Z^2 + (2:ℝ)^114*Z) := by ring
    _ ≤ (gap j:ℝ)^2*(Z/2+(2:ℝ)^114)^2 := mul_le_mul_of_nonneg_left numeric (sq_nonneg _)
    _ = _ := by ring

/-- One common minimizing menu item works for all fixed suffixes. -/
theorem exists_minimizing_block_step {n : ℕ} (hn : 0<n) (P : RankPlacement n → RankPlacement n)
    (j u : ℕ) (large : 9400 ≤ gap j) (ratio : u ≤ 2^16*gap j)
    (Z : ℝ) (zpos : 0 ≤ Z) (initial : meanEnergy P ≤ ((u:ℝ)*Z)^2) :
    ∃ h ∈ choices j, (∀ v ∈ choices j, score P j h ≤ score P j v) ∧
      ∀ suffix : List ℕ, meanEnergy (fun p => sortWord (block j h (P p)) suffix) ≤
        ((gap j:ℝ)*(Z/2+(2:ℝ)^114))^2 := by
  obtain ⟨v,hv,_⟩ := select_actual_linear_block hn P j large
  obtain ⟨h,hm,hmin⟩ := (choices j).exists_min_image (score P j) ⟨v,hv⟩
  exact ⟨h,hm,hmin,minimizing_block_step hn P j u large ratio Z zpos initial h hmin⟩

/-- Total scale charge along a finite trajectory of affine contractions. -/
theorem geometric_budget (Z : ℕ → ℝ) (B : ℝ) (m : ℕ)
    (step : ∀ i<m, Z (i+1) ≤ Z i / 2 + B) :
    (∑ i ∈ range m, Z i) + 2*Z m ≤ 2*Z 0 + 2*(m:ℝ)*B := by
  induction m with
  | zero => simp
  | succ m ih =>
    have prev := ih (fun i hi => step i (by omega))
    have last := step m (by omega)
    simp only [sum_range_succ,Nat.cast_succ]
    linarith

#print axioms exists_minimizing_block_step
#print axioms geometric_budget
end Shellsort.CanonicalWarmStart
