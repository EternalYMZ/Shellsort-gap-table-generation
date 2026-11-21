import Shellsort.ActualMenuMoment

/-! Write the menu probability as a uniform law on fully predrawn vectors. -/
noncomputable section
namespace Shellsort.PredrawnMenuMoment
open Finset Actual214 HarvestMenuBlock HarvestBlockIteration HarvestTenSchedule
open ActualMenuMoment

def Draws : List Stage → Type
  | [] => Unit
  | s::ss => {h // h ∈ choices s.j} × Draws ss

instance drawFinite : (ss : List Stage) → Fintype (Draws ss)
  | [] => inferInstanceAs (Fintype Unit)
  | s::ss => by
    letI := drawFinite ss
    exact inferInstanceAs (Fintype ({h // h ∈ choices s.j} × Draws ss))

def execute {n : ℕ} (p : RankPlacement n) : (ss : List Stage) → Draws ss → RankPlacement n
  | [], _ => p
  | s::ss, (h,ds) => execute (sortWord p (stageWord s h.val)) ss ds

/-- Every vector has the same weight. All menus depend on scale alone. -/
theorem finite_law {n : ℕ} (r H : ℕ) (p : RankPlacement n) (ss : List Stage) :
    (∑ ds : Draws ss, (rms (execute p ss ds)/(endCenter H ss:ℝ))^(r+2)) /
      (Fintype.card (Draws ss):ℝ) = terminalMoment r H p ss := by
  induction ss generalizing H p with
  | nil =>
    change (∑ _ : Unit, (rms p/(H:ℝ))^(r+2)) / (Fintype.card Unit:ℝ) = _
    simp [terminalMoment]
  | cons s ss ih =>
    let G := choices s.j
    let T := fun (h : ℕ) (ds : Draws ss) =>
      (rms (execute (sortWord p (stageWord s h)) ss ds) / (endCenter (gap s.j) ss:ℝ))^(r+2)
    change (∑ pair : (↥G × Draws ss), T pair.1.val pair.2) /
      (Fintype.card (↥G × Draws ss):ℝ) =
      (∑ h ∈ G, terminalMoment r (gap s.j) (sortWord p (stageWord s h)) ss)/(G.card:ℝ)
    rw [Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul, Fintype.card_coe]
    simp_rw [←ih]
    change (∑ h : ↥G, ∑ ds, T h.val ds) / ((G.card:ℝ) * Fintype.card (Draws ss)) =
      (∑ h ∈ G, (∑ ds, T h ds)/(Fintype.card (Draws ss):ℝ))/(G.card:ℝ)
    have ag : (∑ h : ↥G, ∑ ds, T h.val ds) = ∑ h ∈ G, ∑ ds, T h ds :=
      Finset.sum_attach G (fun h => ∑ ds, T h ds)
    rw [←sum_div, ag, div_div, mul_comm]

def normalizedExit {n : ℕ} (H : ℕ) (p : RankPlacement n) (ss : List Stage) (ds : Draws ss) : ℝ :=
  rms (execute p ss ds)/(endCenter H ss:ℝ)

/-- Fraction of the input-independent draw vectors whose actual prefix
    displacement exceeds a specified normalized threshold. -/
theorem fraction_large_prefix {n : ℕ} (hn : 2≤n) (p : RankPlacement n) (r k : ℕ)
    (T : ℝ) (ht : 0<T) :
    let ss := (stages (count n)).take k
    (((univ : Finset (Draws ss)).filter (fun ds => T ≤ normalizedExit n p ss ds)).card:ℝ) /
      (Fintype.card (Draws ss):ℝ) ≤ ((4*(2:ℝ)^(130*(r+2)))/T)^(r+2) := by
  intro ss
  let bad := (univ : Finset (Draws ss)).filter (fun ds => T ≤ normalizedExit n p ss ds)
  let x := normalizedExit n p ss
  have nonneg (ds : Draws ss) : 0≤x ds :=
    div_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg _)
  have mark : (bad.card:ℝ)*T^(r+2) ≤ ∑ ds, (x ds)^(r+2) := by
    calc
      _ = ∑ _ ∈ bad, T^(r+2) := by simp
      _ ≤ ∑ ds ∈ bad, (x ds)^(r+2) := by
        apply sum_le_sum
        intro ds hd
        exact pow_le_pow_left₀ ht.le (mem_filter.mp hd).2 _
      _ ≤ ∑ ds, (x ds)^(r+2) := sum_le_sum_of_subset_of_nonneg (subset_univ _) (by
        intro ds _ _; exact pow_nonneg (nonneg ds) _)
  have bound : (∑ ds, (x ds)^(r+2))/(Fintype.card (Draws ss):ℝ) ≤
      (4*(2:ℝ)^(130*(r+2)))^(r+2) :=
    (finite_law r n p ss).le.trans (actual_prefix_moment hn p r k)
  rw [div_pow]
  apply (le_div_iff₀ (pow_pos ht _)).mpr
  change (bad.card:ℝ)/_ * _ ≤ _
  rw [div_mul_eq_mul_div]
  exact (div_le_div_of_nonneg_right mark (Nat.cast_nonneg _)).trans bound

#print axioms fraction_large_prefix
end Shellsort.PredrawnMenuMoment
