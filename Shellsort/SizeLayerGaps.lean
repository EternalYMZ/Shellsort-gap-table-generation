import Mathlib.Order.Interval.Finset.Nat

/-! Predetermined Shellsort gap tables indexed by the number of keys.
The finite set represents its unique decreasing execution order. At a change
of layer any entries may be rewritten, even when the number of entries grows.
-/

namespace Shellsort.SizeLayer

abbrev Word := Finset ℕ

/-- The restricted class uses positive distinct gaps at most half the input size. -/
def Legal (n : ℕ) (w : Word) : Prop :=
  1 ∈ w ∧ w ⊆ Finset.Icc 1 (n / 2)

/-- A complete rewrite is allowed if the pass count stays fixed or grows by one. -/
def Allowed (u v : Word) : Prop := u.card ≤ v.card ∧ v.card ≤ u.card + 1

theorem allowed_iff_three (u v : Word) :
    Allowed u v ↔ u = v ∨ (u ≠ v ∧ u.card = v.card) ∨ v.card = u.card + 1 := by
  unfold Allowed
  by_cases e : u = v
  · subst v
    simp
  · simp [e]
    omega

/-- A fixed set of admissible integer gaps truncated at the half-size cutoff. -/
def active (keep : ℕ → Bool) (n : ℕ) : Word :=
  (Finset.Icc 1 (n / 2)).filter (fun h => keep h = true)

theorem active_from_even (keep : ℕ → Bool) (k : ℕ) :
    active keep (2*k+1) = active keep (2*k) := by
  have e : (2*k+1)/2 = (2*k)/2 := by omega
  simp only [active, e]

theorem active_to_even (keep : ℕ → Bool) (k : ℕ) :
    active keep (2*k+2) =
      if keep (k+1) = true then insert (k+1) (active keep (2*k+1))
      else active keep (2*k+1) := by
  have e : (2*k+2)/2 = k+1 := by omega
  have f : (2*k+1)/2 = k := by omega
  ext h
  by_cases hh : h = k+1
  · subst h
    split <;> simp_all [active, Finset.mem_Icc]
  · have eqv : h ≤ k+1 ↔ h ≤ k := by omega
    split <;> simp_all [active, Finset.mem_Icc]

/-- An actual path must respect legality separately at each intervening input size. -/
inductive Path (n : ℕ) (u : Word) : ℕ → Word → Prop where
  | start : Path n u 0 u
  | step {t : ℕ} {v w : Word} :
      Path n u t v → Legal (n+t+1) w → Allowed v w → Path n u (t+1) w

private theorem legal_card {n : ℕ} {u : Word} (hu : Legal n u) :
    1 ≤ u.card ∧ u.card ≤ n / 2 := by
  have lo := Finset.card_pos.mpr (show u.Nonempty from ⟨1, hu.1⟩)
  have hi := Finset.card_le_card hu.2
  simpa using And.intro lo hi

private theorem witness {n p : ℕ} (hp : 1 ≤ p) (hn : p ≤ n/2) :
    Legal n (Finset.Icc 1 p) ∧ (Finset.Icc 1 p).card = p := by
  refine ⟨⟨by simpa [Finset.mem_Icc] using hp, ?_⟩, by simp⟩
  intro h hh
  have a := Finset.mem_Icc.mp hh
  exact Finset.mem_Icc.mpr ⟨a.1, a.2.trans hn⟩

private theorem path_counts {n t : ℕ} {u w : Word} (h : Path n u t w) :
    u.card ≤ w.card ∧ w.card ≤ u.card + t := by
  induction h with
  | start => simp
  | step _ _ hs ih =>
    unfold Allowed at hs
    omega

/-- With at least one transition, these are the only restrictions on the endpoint.
Intermediate tables need only be legal. Their costs do not enter the assertion. -/
theorem path_iff {n t : ℕ} {u w : Word} (hu : Legal n u) :
    Path n u (t+1) w ↔
      Legal (n+t+1) w ∧ u.card ≤ w.card ∧ w.card ≤ u.card+(t+1) := by
  constructor
  · intro h
    obtain ⟨lo,hi⟩ := path_counts h
    cases h with
    | step _ hw _ => exact ⟨hw, lo, hi⟩
  · induction t generalizing w with
    | zero =>
      rintro ⟨hw,lo,hi⟩
      exact Path.step Path.start hw ⟨lo, hi⟩
    | succ t ih =>
      rintro ⟨hw,lo,hi⟩
      let q := max u.card (w.card-1)
      have hc := legal_card hu
      have hd := legal_card hw
      have b : q ≤ (n+t+1)/2 := by dsimp [q]; omega
      obtain ⟨hv, hq⟩ := witness (p := q) (by dsimp [q]; omega) b
      have prev : Path n u (t+1) (Finset.Icc 1 q) := by
        apply ih
        refine ⟨hv, ?_, ?_⟩ <;> rw [hq] <;> dsimp [q] <;> omega
      apply Path.step prev hw
      unfold Allowed
      rw [hq]
      dsimp [q]
      omega

/-- Sum of the edge quotas floor((upper-1)/lower), ending with the unit gap.
The intermediate gaps are listed in execution order. -/
def edgeSum (upper : ℕ) : List ℕ → ℕ
  | [] => upper-1
  | h :: hs => (upper-1)/h + edgeSum h hs

private theorem succ_le_two_pow (k : ℕ) : k+1 ≤ 2^k := by
  induction k with
  | zero => decide
  | succ k ih => rw [pow_succ]; omega

private theorem edge_le (upper h : ℕ) (hp : 0 < h) :
    upper ≤ 2^((upper-1)/h)*h := by
  have hd := Nat.div_add_mod (upper-1) h
  have hm := Nat.mod_lt (upper-1) hp
  have hb : upper ≤ ((upper-1)/h+1)*h := by
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm ((upper-1)/h) h]
    omega
  exact hb.trans (Nat.mul_le_mul_right h (succ_le_two_pow _))

/-- Integer form of the ceil(log2(B+1)) lower bound, using upper = B+1. -/
theorem upper_le_two_pow_edgeSum (upper : ℕ) (hs : List ℕ)
    (hp : ∀ h ∈ hs, 0 < h) : upper ≤ 2^(edgeSum upper hs) := by
  induction hs generalizing upper with
  | nil =>
    simpa [edgeSum] using edge_le upper 1 (by decide)
  | cons h hs ih =>
    have a := edge_le upper h (hp h (by simp))
    have b := ih h (fun k hk => hp k (by simp [hk]))
    simpa [edgeSum, pow_add] using a.trans (Nat.mul_le_mul_left _ b)

/-- The powers of two between 2 and 2^k, largest first. -/
def dyadicInterior : ℕ → List ℕ
  | 0 => []
  | k+1 => 2^(k+1) :: dyadicInterior k

theorem dyadicInterior_bounds (k : ℕ) :
    ∀ h ∈ dyadicInterior k, 1 < h ∧ h ≤ 2^k := by
  induction k with
  | zero => simp [dyadicInterior]
  | succ k ih =>
    intro h hm
    have pos := Nat.two_pow_pos k
    simp only [dyadicInterior, List.mem_cons] at hm
    rcases hm with rfl | hm
    · rw [pow_succ]; omega
    · have := ih h hm
      rw [pow_succ]; omega

theorem dyadicInterior_desc (k : ℕ) :
    (dyadicInterior k).Pairwise (· > ·) := by
  induction k with
  | zero => simp [dyadicInterior]
  | succ k ih =>
    apply List.Pairwise.cons _ ih
    intro h hm
    have := (dyadicInterior_bounds k h hm).2
    have := Nat.two_pow_pos k
    rw [pow_succ]; omega

/-- If 2^k < upper ≤ 2^(k+1), descending powers of two attain score k+1. -/
theorem dyadic_edgeSum (k upper : ℕ) (lo : 2^k < upper) (hi : upper ≤ 2^(k+1)) :
    edgeSum upper (dyadicInterior k) = k+1 := by
  induction k generalizing upper with
  | zero =>
    change 1 < upper at lo
    change upper ≤ 2 at hi
    change upper-1 = 1
    omega
  | succ k ih =>
    have p := Nat.two_pow_pos k
    have q : (upper-1)/2^(k+1) = 1 := by
      apply Nat.div_eq_of_lt_le
      · simp only [Nat.one_mul]; omega
      · rw [pow_succ (2 : ℕ) (k+1)] at hi; omega
    have r := ih (2^(k+1)) (by rw [pow_succ]; omega) (by rfl)
    simp only [dyadicInterior, edgeSum, q]
    omega

end Shellsort.SizeLayer
