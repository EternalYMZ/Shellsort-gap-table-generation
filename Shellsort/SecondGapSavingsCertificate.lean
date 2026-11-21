import Shellsort.KnuthPairFiniteLower

/-! Finite arithmetic for the uniform pieces in the 3g insertion.
The connection to an actual row uses Knuth's finite mean for the final
inversion count. Superadditivity expresses legal partial sorting on pieces. -/
noncomputable section
namespace Shellsort.SecondGapSavingsCertificate
open KnuthPairFiniteLower

/-- Initial mean inversions minus mean shifts in both local passes (3,1). -/
def uniformFormula (s : ℕ) : ℝ :=
  let t : ℝ := (s/3 : ℕ)
  let j : ℝ := (s%3 : ℕ)
  ((s:ℝ)*(s-1) - (3-j)*t*(t-1) - j*t*(t+1))/4 - finiteMean 3 (s/3) (s%3)

private theorem c2 : Nat.choose 4 2 = 6 := by decide
private theorem c3 : Nat.choose 6 3 = 20 := by decide
private theorem c4 : Nat.choose 8 4 = 70 := by decide
private theorem c5 : Nat.choose 10 5 = 252 := by decide
private theorem c6 : Nat.choose 12 6 = 924 := by decide
private theorem c7 : Nat.choose 14 7 = 3432 := by decide

set_option maxHeartbeats 2500000 in
theorem short_piece (s : ℕ) (h : s < 21) :
    157*(s:ℝ)-972 ≤ 70*uniformFormula s := by
  interval_cases s <;>
    norm_num [uniformFormula, finiteMean, pairCount, equalPair, unequalPair, Nat.centralBinom,
      c2, c3, c4, c5, c6, c7]

theorem full_piece : (157:ℝ)*21 ≤ 70*uniformFormula 21 := by
  norm_num [uniformFormula, finiteMean, pairCount, equalPair, unequalPair, Nat.centralBinom, c7]

/-- The numerical identity for true mean savings is needed only through 21. -/
theorem all_pieces (saving : ℕ → ℝ)
    (small : ∀ s ≤ 21, saving s = uniformFormula s)
    (join : ∀ a b, saving a + saving b ≤ saving (a+b)) (s : ℕ) :
    157*(s:ℝ)-972 ≤ 70*saving s := by
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    by_cases hs : s < 21
    · rw [small s (by omega)]
      exact short_piece s hs
    · let b := s-21
      have hb : b<s := by dsimp [b]; omega
      have split : 21+b=s := by dsimp [b]; omega
      have sizes : (21:ℝ)+b=s := by exact_mod_cast split
      have rep := join 21 b
      rw [split] at rep
      have large := full_piece
      rw [←small 21 (by omega)] at large
      linarith [ih b hb]

/-- Finite arithmetic giving the strict comparison for a list of at most 9g
homogeneous pieces. The record-minimum correction costs at most n-g. -/
theorem strict_gain (saving : ℕ → ℝ)
    (small : ∀ s ≤ 21, saving s = uniformFormula s)
    (join : ∀ a b, saving a + saving b ≤ saving (a+b))
    (pieces : List ℕ) (g : ℕ) (gp : 0<g)
    (few : pieces.length ≤ 9*g) (many : 100*g ≤ pieces.sum) :
    0 < (pieces.map saving).sum - ((pieces.sum:ℝ)-g) := by
  have sum_bound (p : List ℕ) :
      157*(p.sum:ℝ)-972*(p.length:ℝ) ≤ 70*(p.map saving).sum := by
    induction p with
    | nil => simp
    | cons a p ih =>
      simp only [List.sum_cons, List.length_cons, List.map_cons, Nat.cast_add, Nat.cast_one]
      linarith [all_pieces saving small join a]
  have fewR : (pieces.length:ℝ) ≤ 9*g := by exact_mod_cast few
  have manyR : 100*(g:ℝ) ≤ pieces.sum := by exact_mod_cast many
  have gpR : 0<(g:ℝ) := by exact_mod_cast gp
  linarith [sum_bound pieces]

#print axioms strict_gain
end Shellsort.SecondGapSavingsCertificate
