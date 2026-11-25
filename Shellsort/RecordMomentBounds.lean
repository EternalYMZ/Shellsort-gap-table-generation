import Shellsort.InsertionComparisons

/-! Two-moment bounds for the event that an insertion key has no smaller predecessor. -/

namespace Shellsort.RecordMomentBounds

open Finset

/-- The existing executable counter charges each larger predecessor and
one stopping test precisely when a smaller predecessor exists. The
predecessor list is stored from right to left. -/
theorem executed_charge {α : Type*} [LinearOrder α] (a : α) (l : List α)
    (sorted : l.Pairwise (fun x y => y ≤ x)) (fresh : a ∉ l) :
    (insertCompared a l).comparisons + (if smallerCount a l = 0 then 1 else 0) +
      smallerCount a l = l.length + 1 := by
  induction l with
  | nil => simp [insertCompared, smallerCount]
  | cons b l ih =>
    obtain ⟨head, tail⟩ := List.pairwise_cons.mp sorted
    have hne : a ≠ b := fun h => fresh (h ▸ List.mem_cons_self)
    by_cases hab : a < b
    · specialize ih tail (fun h => fresh (List.mem_cons_of_mem _ h))
      simp only [insertCompared, hab, ite_true, List.length_cons]
      have eq : smallerCount a (b :: l) = smallerCount a l := by
        simp [smallerCount, not_lt.mpr hab.le]
      rw [eq]
      omega
    · have hba := lt_of_le_of_ne (le_of_not_gt hab) (Ne.symm hne)
      have allSmall : l.filter (fun x => decide (x < a)) = l :=
        List.filter_eq_self.mpr (fun x hx => by simpa using lt_of_le_of_lt (head x hx) hba)
      simp [insertCompared, smallerCount, hab, hba, allSmall, Nat.add_comm 1]

/-- Integer counts skip the open interval between consecutive integers. -/
private theorem adjacent_product_nonneg (r k : ℕ) :
    0 ≤ ((r : ℝ) - k) * (r - k - 1) := by
  rcases le_or_gt r k with hr | hr
  · have h : (r : ℝ) ≤ k := by exact_mod_cast hr
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  · have h : (k : ℝ) + 1 ≤ r := by exact_mod_cast hr
    exact mul_nonneg (by linarith) (by linarith)

/-- With a finite law on counts in [0,L], the atom at zero lies between
the two quadratic envelopes. The inequalities are multiplied by their
positive denominators. Any positive integer k gives an upper envelope. -/
private theorem scaled_record_bounds {ι : Type*} [Fintype ι] (w : ι → ℝ) (r : ι → ℕ)
    (nonneg : ∀ i, 0 ≤ w i) (mass : ∑ i, w i = 1)
    (L k : ℕ) (support : ∀ i, r i ≤ L) :
    let μ := ∑ i, w i * (r i : ℝ)
    let ν := ∑ i, w i * (r i : ℝ) * (r i - 1)
    let p := ∑ i, w i * (if r i = 0 then 1 else 0 : ℝ)
    (L : ℝ) * (1 - μ) + ν ≤ L * p ∧
      (k : ℝ) * (k + 1) * p ≤ k * (k + 1) - 2 * k * μ + ν := by
  dsimp only
  have lo (i : ι) :
      (L : ℝ) * (w i - w i * (r i : ℝ)) + w i * r i * (r i - 1) ≤
        L * (w i * (if r i = 0 then 1 else 0 : ℝ)) := by
    by_cases hz : r i = 0
    · simp [hz]
    · have hr : (1 : ℝ) ≤ r i := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
      have hmax : (r i : ℝ) ≤ L := by exact_mod_cast support i
      have h := mul_nonneg (nonneg i) (mul_nonneg (sub_nonneg.mpr hr) (sub_nonneg.mpr hmax))
      simp only [hz, ite_false, mul_zero]
      linarith only [h]
  have hi (i : ι) :
      (k : ℝ) * (k + 1) * (w i * (if r i = 0 then 1 else 0 : ℝ)) ≤
        k * (k + 1) * w i - 2 * k * (w i * r i) + w i * r i * (r i - 1) := by
    by_cases hz : r i = 0
    · simp [hz]
    · have h := mul_nonneg (nonneg i) (adjacent_product_nonneg (r i) k)
      simp only [hz, ite_false, mul_zero]
      linarith only [h]
  constructor
  · have h := sum_le_sum (s := (univ : Finset ι)) (fun i _ => lo i)
    simpa only [sum_add_distrib, ← mul_sum, sum_sub_distrib, mass] using h
  · have h := sum_le_sum (s := (univ : Finset ι)) (fun i _ => hi i)
    simpa only [sum_add_distrib, sum_sub_distrib, ← mul_sum, mass, mul_one] using h

/-- A finite law's true first and second factorial moments bound the record
probability. The upper bound specializes to the Dawson–Sankoff envelope
at k = floor (1 + ν / μ) when μ > 0. -/
theorem record_bounds {ι : Type*} [Fintype ι] (w : ι → ℝ) (r : ι → ℕ)
    (nonneg : ∀ i, 0 ≤ w i) (mass : ∑ i, w i = 1)
    (L k : ℕ) (hL : 0 < L) (hk : 0 < k) (support : ∀ i, r i ≤ L) :
    let μ := ∑ i, w i * (r i : ℝ)
    let ν := ∑ i, w i * (r i : ℝ) * (r i - 1)
    let p := ∑ i, w i * (if r i = 0 then 1 else 0 : ℝ)
    max 0 (1 - μ + ν / L) ≤ p ∧
      p ≤ 1 - 2 * μ / (k + 1) + ν / (k * (k + 1)) := by
  dsimp only
  obtain ⟨lo, hi⟩ := scaled_record_bounds w r nonneg mass L k support
  have Lpos : (0 : ℝ) < L := by exact_mod_cast hL
  have kpos : (0 : ℝ) < k := by exact_mod_cast hk
  have succPos : (0 : ℝ) < k + 1 := by linarith
  have recNonneg (i : ι) : 0 ≤ w i * (if r i = 0 then 1 else 0 : ℝ) := by
    split <;> simp [nonneg]
  constructor
  · apply max_le (sum_nonneg fun i _ => recNonneg i)
    apply (le_sub_iff_add_le').mp
    apply (div_le_iff₀ Lpos).mpr
    linarith only [lo]
  · apply (sub_le_iff_le_add').mp
    apply (le_div_iff₀ (mul_pos kpos succPos)).mpr
    have cancel : (2 * (∑ i, w i * (r i : ℝ)) / (k + 1)) * ((k : ℝ) * (k + 1)) =
        2 * k * (∑ i, w i * (r i : ℝ)) := by
      rw [mul_comm (k : ℝ), ← mul_assoc, div_mul_cancel₀ _ succPos.ne']
      ring
    rw [sub_mul, sub_mul, one_mul, cancel]
    linarith only [hi]

/-- For an insertion facing L predecessors with r smaller keys, the charge
is L - r shifts plus the terminating comparison exactly when r > 0.
The same true moments therefore give a comparison interval. -/
theorem comparison_bounds {ι : Type*} [Fintype ι] (w : ι → ℝ) (r : ι → ℕ)
    (nonneg : ∀ i, 0 ≤ w i) (mass : ∑ i, w i = 1)
    (L k : ℕ) (hL : 0 < L) (hk : 0 < k) (support : ∀ i, r i ≤ L) :
    let μ := ∑ i, w i * (r i : ℝ)
    let ν := ∑ i, w i * (r i : ℝ) * (r i - 1)
    let cost := ∑ i, w i * ((L : ℝ) - r i + 1 - (if r i = 0 then 1 else 0 : ℝ))
    L - μ + 1 - (1 - 2 * μ / (k + 1) + ν / (k * (k + 1))) ≤ cost ∧
      cost ≤ L - μ + 1 - max 0 (1 - μ + ν / L) := by
  dsimp only
  obtain ⟨lo, hi⟩ := record_bounds w r nonneg mass L k hL hk support
  simp only [mul_sub, mul_add, sum_sub_distrib, sum_add_distrib,
    ← sum_mul, mass, one_mul, mul_one] at lo hi ⊢
  constructor <;> linarith only [lo, hi]

end Shellsort.RecordMomentBounds
