import Shellsort.RoughGapPredeterminedSelection

/-! Canonical finite offline rule. Integer scores avoid real-number comparison.
The prefix is fixed before any input, so expectation is over initial permutations.
The noncomputable declarations below specify the rule for the abstract rank map;
they are not an efficient implementation of permutation enumeration. -/
noncomputable section
namespace Shellsort.RoughGapCanonical
open Finset RoughGapSelection

def score {n : ℕ} (P : RankPlacement n → RankPlacement n) (h : ℕ) : ℤ :=
  ∑ p : RankPlacement n, RoughGapScaleAssembly.squareDisplacement (gapSort (P p) h)

def meanEnergy {n : ℕ} (P : RankPlacement n → RankPlacement n) (h : ℕ) : ℝ :=
  uniformAverage (fun p => energy (gapSort (P p) h))

theorem meanEnergy_eq {n : ℕ} (P : RankPlacement n → RankPlacement n) (h : ℕ) :
    meanEnergy P h = ((score P h : ℤ) : ℝ) / n / n.factorial := by
  simp [meanEnergy, uniformAverage, energy, score, sum_div]

private def winners (G : Finset ℕ) (f : ℕ → ℤ) := G.filter fun h => ∀ j ∈ G, f h ≤ f j

private theorem winners_nonempty (G : Finset ℕ) (f : ℕ → ℤ) (ne : G.Nonempty) :
    (winners G f).Nonempty := by
  obtain ⟨h, hh, hbest⟩ := G.exists_min_image f ne
  exact ⟨h, mem_filter.mpr ⟨hh, hbest⟩⟩

/-- Select the numerically smallest minimizer of the integer score. -/
def pick {n : ℕ} (P : RankPlacement n → RankPlacement n) (G : Finset ℕ) (ne : G.Nonempty) : ℕ :=
  (winners G (score P)).min' (winners_nonempty G (score P) ne)

theorem pick_spec {n : ℕ} (P : RankPlacement n → RankPlacement n) (G : Finset ℕ) (ne : G.Nonempty) :
    pick P G ne ∈ G ∧ (∀ j ∈ G, score P (pick P G ne) ≤ score P j) ∧
    (∀ j ∈ G, score P j = score P (pick P G ne) → pick P G ne ≤ j) := by
  have w := min'_mem (winners G (score P)) (winners_nonempty G (score P) ne)
  change pick P G ne ∈ G.filter _ at w
  obtain ⟨mem, minimal⟩ := mem_filter.mp w
  refine ⟨mem, minimal, ?_⟩
  intro j hj eq
  apply min'_le
  exact mem_filter.mpr ⟨hj, fun i hi => eq ▸ minimal i hi⟩

theorem pick_mean_le {n : ℕ} (P : RankPlacement n → RankPlacement n) (G : Finset ℕ) (ne : G.Nonempty)
    {j : ℕ} (hj : j ∈ G) : meanEnergy P (pick P G ne) ≤ meanEnergy P j := by
  rw [meanEnergy_eq, meanEnergy_eq]
  gcongr
  exact_mod_cast (pick_spec P G ne).2.1 j hj

theorem pick_le_menu_mean {n : ℕ} (P : RankPlacement n → RankPlacement n) (G : Finset ℕ)
    (ne : G.Nonempty) : meanEnergy P (pick P G ne) ≤ (∑ j ∈ G, meanEnergy P j) / G.card := by
  apply (le_div_iff₀ (show 0 < (G.card : ℝ) by exact_mod_cast card_pos.mpr ne)).mpr
  have h := sum_le_sum (s := G) (fun j hj => pick_mean_le P G ne hj)
  simpa [mul_comm] using h

theorem pick_inherits_statewise_bound {n : ℕ} (P : RankPlacement n → RankPlacement n) (G : Finset ℕ)
    (ne : G.Nonempty) (bound : RankPlacement n → ℝ)
    (step : ∀ p, (∑ h ∈ G, energy (gapSort (P p) h)) / G.card ≤ bound (P p)) :
    meanEnergy P (pick P G ne) ≤ uniformAverage (fun p => bound (P p)) := by
  obtain ⟨h, hh, hb⟩ := select_common_gap P G ne bound step
  exact (pick_mean_le P G ne hh).trans hb

#print axioms meanEnergy_eq
#print axioms pick_spec
#print axioms pick_mean_le
#print axioms pick_le_menu_mean
#print axioms pick_inherits_statewise_bound
end Shellsort.RoughGapCanonical
