import Mathlib

/-! Arithmetic and minimization consequences of the endpoint-pair cost formulas.
The formulas themselves are explicit hypotheses on the rational mean cost. -/
namespace Shellsort.FirstGapOptimumThreshold

abbrev Word := List ℕ
def Legal (n : ℕ) : Word → Prop
  | [] => False
  | g::v => 0 < g ∧ g < n ∧ (g::v).getLast? = some 1 ∧ (g::v).Pairwise (· > ·)

def Best (n : ℕ) (score : Word → ℚ) (w : Word) : Prop :=
  Legal n w ∧ ∀ u, Legal n u → score w ≤ score u

def steps (n g : ℕ) := (n-1)/g
def live (n g : ℕ) := n - steps n g * g

def EndpointFormula (n : ℕ) (score : Word → ℚ) (cut : ℕ) : Prop :=
  ∀ g v, Legal n (g::v) → 2 ≤ steps n g →
    score ((steps n g * g)::g::v) - score (g::v) =
      (live n g : ℚ) * ((cut : ℚ) - steps n g) / 3

private theorem new_legal {n g : ℕ} {v : Word} (hw : Legal n (g::v))
    (ht : 2 ≤ steps n g) : Legal n ((steps n g*g)::g::v) := by
  obtain ⟨hg,hn,hl,hp⟩ := hw
  have hlt : g < steps n g * g := by
    have h := Nat.mul_le_mul_right g ht
    omega
  have hmax := Nat.div_mul_le_self (n-1) g
  change steps n g*g ≤ n-1 at hmax
  refine ⟨by omega, by omega, ?_, List.pairwise_cons.mpr ⟨?_, hp⟩⟩
  · simpa using hl
  · intro a ha
    rcases List.mem_cons.mp ha with rfl|ha
    · exact hlt
    · exact lt_trans ((List.pairwise_cons.mp hp).1 _ ha) hlt

private theorem live_pos {n g : ℕ} {v : Word} (hw : Legal n (g::v)) : 0 < live n g := by
  obtain ⟨hg,hn,_,_⟩ := hw
  have hmax := Nat.div_mul_le_self (n-1) g
  unfold live steps
  omega

private theorem weak_head_bound {n g cut : ℕ} {score : Word → ℚ} {v : Word}
    (hcut : 1 ≤ cut) (hform : EndpointFormula n score cut) (hw : Best n score (g::v)) :
    n ≤ (cut+1)*g := by
  by_contra! h
  have hg : 0 < g := hw.1.1
  have ht : cut+1 ≤ steps n g := (Nat.le_div_iff_mul_le hg).2 (by omega)
  have htwo : 2 ≤ steps n g := by omega
  have he := hform g v hw.1 htwo
  have hopt := hw.2 _ (new_legal hw.1 htwo)
  have hn : (0 : ℚ) < live n g := by exact_mod_cast live_pos hw.1
  have hc : (cut : ℚ) < steps n g := by exact_mod_cast (show cut < steps n g by omega)
  have hneg := mul_neg_of_pos_of_neg hn (sub_neg.mpr hc)
  linarith

/-- Every mean-comparison minimizer starts with g ≥ ceil(n/5), assuming the comparison formula. -/
theorem comparison_head_bound {n g : ℕ} {score : Word → ℚ} {v : Word}
    (hf : EndpointFormula n score 4) (hw : Best n score (g::v)) : n ≤ 5*g :=
  weak_head_bound (by decide) hf hw

/-- Every mean-movement minimizer starts with g ≥ ceil(n/2), assuming the movement formula. -/
theorem movement_head_bound {n g : ℕ} {score : Word → ℚ} {v : Word}
    (hf : EndpointFormula n score 1) (hw : Best n score (g::v)) : n ≤ 2*g :=
  weak_head_bound (by decide) hf hw

/-- The upper endpoint n=5g remains in this interval, while n=4g does not. -/
theorem twin_interval {n g : ℕ} {score : Word → ℚ} {v : Word} (hf : EndpointFormula n score 4)
    (hw : Legal n (g::v)) (lo : 4*g<n) (hi : n≤5*g) :
    score ((4*g)::g::v)=score (g::v) ∧
      (Best n score ((4*g)::g::v) ↔ Best n score (g::v)) := by
  have hg := hw.1
  have h1 : 4 ≤ (n-1)/g := (Nat.le_div_iff_mul_le hg).2 (by omega)
  have h2 : (n-1)/g < 5 := (Nat.div_lt_iff_lt_mul hg).2 (by omega)
  have ht : steps n g = 4 := by unfold steps; omega
  have he := hf g v hw (by omega)
  rw [ht] at he
  have eq : score ((4*g)::g::v) = score (g::v) := by push_cast at he; linarith
  have hlegal := new_legal hw (by omega)
  rw [ht] at hlegal
  constructor
  · exact eq
  · constructor
    · rintro ⟨_,h⟩
      exact ⟨hw,by simpa [eq] using h⟩
    · rintro ⟨_,h⟩
      exact ⟨hlegal,by simpa [eq] using h⟩

/-- From any minimizer one can produce a minimizer with first gap ≥ ceil(n/4). -/
theorem large_head_representative {n g : ℕ} {score : Word → ℚ} {v : Word}
    (hf : EndpointFormula n score 4) (hw : Best n score (g::v)) :
    ∃ g' v', Best n score (g'::v') ∧ n ≤ 4*g' := by
  by_cases h : n ≤ 4*g
  · exact ⟨g,v,hw,h⟩
  · have hi := comparison_head_bound hf hw
    have he := twin_interval hf hw.1 (by omega) hi
    exact ⟨4*g,g::v,he.2.mpr hw,by omega⟩

end Shellsort.FirstGapOptimumThreshold
