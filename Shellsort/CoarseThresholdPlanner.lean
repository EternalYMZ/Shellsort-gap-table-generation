import Shellsort.ThresholdContraction

/-! Approximate checkpoint footrules from sampled rank thresholds.
The sampled statistic depends only on the low-key sets at the chosen thresholds. -/
noncomputable section
namespace Shellsort
open scoped BigOperators

/-- Low keys at or beyond the physical cut, with exactly k low ranks when k ≤ n. -/
def crossingSlots {n : ℕ} (p : RankPlacement n) (k : ℕ) : Finset (Fin n) :=
  (thresholdSet p k).filter (fun i => k ≤ i.val)

private theorem crossingSlots_mem {n : ℕ} (p : RankPlacement n) (k : ℕ) (i : Fin n) :
    i ∈ crossingSlots p k ↔ (p.symm i).val < k ∧ k ≤ i.val := by
  simp [crossingSlots, threshold_mem]

private theorem crossing_card_pair_le {n : ℕ} (p : RankPlacement n) {k l : ℕ}
    (hkl : k ≤ l) :
    (crossingSlots p k).card ≤ (crossingSlots p l).card + (l-k) ∧
    (crossingSlots p l).card ≤ (crossingSlots p k).card + (l-k) := by
  classical
  let A := crossingSlots p k
  let B := crossingSlots p l
  have hi : (A \ B).card ≤ (Finset.Ico k l).card := by
    apply Finset.card_le_card_of_injOn Fin.val _ Fin.val_injective.injOn
    intro i hi
    obtain ⟨ha,hb⟩ := Finset.mem_sdiff.mp hi
    rw [show A = crossingSlots p k from rfl, crossingSlots_mem] at ha
    rw [show B = crossingSlots p l from rfl, crossingSlots_mem] at hb
    exact Finset.mem_Ico.mpr ⟨ha.2, by omega⟩
  have hj : (B \ A).card ≤ (Finset.Ico k l).card := by
    apply Finset.card_le_card_of_injOn (fun i : Fin n => (p.symm i).val) _
      (Fin.val_injective.comp p.symm.injective).injOn
    intro i hi
    obtain ⟨hb,ha⟩ := Finset.mem_sdiff.mp hi
    rw [show A = crossingSlots p k from rfl, crossingSlots_mem] at ha
    rw [show B = crossingSlots p l from rfl, crossingSlots_mem] at hb
    change (p.symm i).val ∈ Finset.Ico k l
    exact Finset.mem_Ico.mpr ⟨by omega, hb.1⟩
  rw [Nat.card_Ico] at hi hj
  have h₁ := Finset.card_sdiff_add_card_inter A B
  have h₂ := Finset.card_sdiff_add_card_inter B A
  rw [Finset.inter_comm B A] at h₂
  change A.card ≤ B.card + (l-k) ∧ B.card ≤ A.card + (l-k)
  omega

/-- Varying the cut by d ranks changes its one-sided crossing count by at most d. -/
theorem crossingSlots_card_lipschitz {n : ℕ} (p : RankPlacement n) (k l : ℕ) :
    |((crossingSlots p k).card : ℝ) - (crossingSlots p l).card| ≤ |(k : ℝ)-l| := by
  wlog hkl : k ≤ l generalizing k l
  · rw [abs_sub_comm, abs_sub_comm (k : ℝ)]
    exact this l k (by omega)
  obtain ⟨ha,hb⟩ := crossing_card_pair_le p hkl
  have hk : (k : ℝ) ≤ l := by exact_mod_cast hkl
  rw [abs_of_nonpos (sub_nonpos.mpr hk)]
  have ha' : ((crossingSlots p k).card : ℝ) ≤ (crossingSlots p l).card + ((l-k : ℕ) : ℝ) := by
    exact_mod_cast ha
  have hb' : ((crossingSlots p l).card : ℝ) ≤ (crossingSlots p k).card + ((l-k : ℕ) : ℝ) := by
    exact_mod_cast hb
  rw [Nat.cast_sub hkl] at ha' hb'
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Quadrature based on the low-key slots at q(1), ..., q(n); repeated cuts
contribute their multiplicities. -/
def sampledFootrule {n : ℕ} (p : RankPlacement n) (q : ℕ → ℕ) : ℝ :=
  2 * ∑ t : Fin n, ((crossingSlots p (q (t.val+1))).card : ℝ)

def cutGridError (n : ℕ) (q : ℕ → ℕ) : ℝ :=
  2 * ∑ t : Fin n, |((t.val+1 : ℕ) : ℝ)-(q (t.val+1) : ℝ)|

theorem footrule_sampledFootrule_error {n : ℕ} (p : RankPlacement n) (q : ℕ → ℕ) :
    |footrule p - sampledFootrule p q| ≤ cutGridError n q := by
  have hc (t : Fin n) : rightCutCount p t = (crossingSlots p (t.val+1)).card := by
    unfold rightCutCount crossingSlots
    congr 1
  rw [footrule_eq_two_sum_rightCuts]
  simp_rw [hc]
  unfold sampledFootrule cutGridError
  rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2), ← Finset.sum_sub_distrib]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact (Finset.abs_sum_le_sum_abs ..).trans
    (Finset.sum_le_sum (fun t _ => crossingSlots_card_lipschitz p (t.val+1) (q (t.val+1))))

/-- Initial coarse labels suffice to determine the sampled score after every fixed word. -/
theorem sortWord_sampledFootrule_eq {n : ℕ} (p r : RankPlacement n)
    (w : List ℕ) (q : ℕ → ℕ)
    (h : ∀ t : Fin n, thresholdSet p (q (t.val+1)) = thresholdSet r (q (t.val+1))) :
    sampledFootrule (sortWord p w) q = sampledFootrule (sortWord r w) q := by
  unfold sampledFootrule crossingSlots
  simp_rw [sortWord_threshold_commutes, h]

/-- A certificate minimizer has terminal footrule at most 2E above any competitor. -/
theorem sampledFootrule_choice_regret {n : ℕ} (p : RankPlacement n) (a b : List ℕ)
    (q : ℕ → ℕ)
    (hab : sampledFootrule (sortWord p a) q ≤ sampledFootrule (sortWord p b) q) :
    footrule (sortWord p a) ≤ footrule (sortWord p b) + 2 * cutGridError n q := by
  obtain ⟨_, h₁⟩ := abs_le.mp (footrule_sampledFootrule_error (sortWord p a) q)
  obtain ⟨h₂, _⟩ := abs_le.mp (footrule_sampledFootrule_error (sortWord p b) q)
  linarith

/-- Round down to an observed boundary between consecutive rank blocks. -/
def rankGrid (m k : ℕ) : ℕ := k / m * m

theorem sortWord_sampledFootrule_eq_of_rankBlocks {n m : ℕ} (hm : 0 < m)
    (p r : RankPlacement n) (w : List ℕ)
    (h : ∀ i : Fin n, (p.symm i).val / m = (r.symm i).val / m) :
    sampledFootrule (sortWord p w) (rankGrid m) =
      sampledFootrule (sortWord r w) (rankGrid m) := by
  apply sortWord_sampledFootrule_eq
  intro t
  ext i
  simp only [threshold_mem, rankGrid, ← Nat.div_lt_iff_lt_mul hm, h]

theorem cutGridError_rankGrid (n m : ℕ) :
    cutGridError n (rankGrid m) = 2 * ∑ t : Fin n, (((t.val+1) % m : ℕ) : ℝ) := by
  unfold cutGridError rankGrid
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  have hd : (t.val+1)/m*m + (t.val+1)%m = t.val+1 :=
    Nat.div_add_mod' .. 
  have hd' : (((t.val+1)/m*m : ℕ) : ℝ) + (((t.val+1)%m : ℕ) : ℝ) =
      ((t.val+1 : ℕ) : ℝ) := by exact_mod_cast hd
  rw [← hd', add_sub_cancel_left, abs_of_nonneg (Nat.cast_nonneg _)]

theorem cutGridError_rankGrid_le (n m : ℕ) (hm : 0 < m) :
    cutGridError n (rankGrid m) ≤ 2 * n * ((m-1 : ℕ) : ℝ) := by
  rw [cutGridError_rankGrid, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    _ ≤ ∑ _ : Fin n, ((m-1 : ℕ) : ℝ) := Finset.sum_le_sum (fun t _ => by
      exact_mod_cast (show (t.val+1)%m ≤ m-1 by have := Nat.mod_lt (t.val+1) hm; omega))
    _ = _ := by simp

end Shellsort
end
