import Shellsort.Actual214Arithmetic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.GCD.Basic

/-! A deterministic, two-term continuation of the 107/50 gap rule. -/

namespace Shellsort.OnlineTriple

/-- The first admissible value exists, even for the auxiliary pair (0,0). -/
theorem exists_next (x y : ℕ) :
    ∃ z, Actual214.nextGap y ≤ z ∧ (x.gcd y).Coprime z := by
  by_cases hd : x.gcd y = 0
  · obtain ⟨rfl, rfl⟩ := Nat.gcd_eq_zero_iff.mp hd
    exact ⟨1, by decide, by decide⟩
  · have hp : 0 < x.gcd y := Nat.pos_of_ne_zero hd
    let t := Actual214.nextGap y
    refine ⟨1 + t * x.gcd y, ?_, ?_⟩
    · have := Nat.le_mul_of_pos_right t hp
      change t ≤ 1 + t * x.gcd y
      omega
    · exact (Nat.coprime_add_mul_right_right (x.gcd y) 1 t).mpr
        (Nat.coprime_one_right _)

/-- The smallest z at or above the proposed gap with gcd(x,y,z)=1. -/
def next (x y : ℕ) : ℕ := Nat.find (exists_next x y)

theorem next_spec (x y : ℕ) :
    Actual214.nextGap y ≤ next x y ∧ (x.gcd y).Coprime (next x y) :=
  Nat.find_spec (exists_next x y)

theorem next_min {x y z : ℕ} (hz : Actual214.nextGap y ≤ z)
    (h : (x.gcd y).Coprime z) : next x y ≤ z :=
  Nat.find_min' (exists_next x y) ⟨hz, h⟩

theorem next_eq_proposal_iff (x y : ℕ) :
    next x y = Actual214.nextGap y ↔ (x.gcd y).Coprime (Actual214.nextGap y) := by
  constructor
  · intro heq
    simpa only [← heq] using (next_spec x y).2
  · intro hok
    exact Nat.le_antisymm (next_min (Nat.le_refl _) hok) (next_spec x y).1

/-- Consecutive terms of the infinite gap sequence, starting at (1,4). -/
def pair : ℕ → ℕ × ℕ
  | 0 => (1,4)
  | j+1 => ((pair j).2, next (pair j).1 (pair j).2)

def gap (j : ℕ) : ℕ := (pair j).1

@[simp] theorem gap_zero : gap 0 = 1 := rfl
@[simp] theorem gap_one : gap 1 = 4 := rfl

theorem gap_rec (j : ℕ) : gap (j+2) = next (gap j) (gap (j+1)) := rfl

theorem consecutive_triple_gcd (j : ℕ) :
    ((gap j).gcd (gap (j+1))).gcd (gap (j+2)) = 1 :=
  (next_spec (gap j) (gap (j+1))).2

theorem gap_strict (j : ℕ) : gap j < gap (j+1) := by
  cases j with
  | zero => decide
  | succ i =>
    have ht := (Actual214.scaled_next_bounds (gap (i+1))).1
    have hn := (next_spec (gap i) (gap (i+1))).1
    rw [gap_rec]
    omega

end Shellsort.OnlineTriple
