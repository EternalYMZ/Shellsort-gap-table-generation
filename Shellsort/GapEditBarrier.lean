import Mathlib.Data.List.Chain
import Mathlib.Data.Set.Basic

/-! A finite edit path crossing a cut visits a vertex of its outer boundary. -/
namespace Shellsort.GapEditBarrier

variable {α β : Type*} {edit : α → α → Prop} {S : Set α}
  {start target : α} {visits : List α}

/-- Incoming edges are directed from the inside of the cut. -/
def OuterBoundary (edit : α → α → Prop) (S : Set α) (y : α) : Prop :=
  y ∉ S ∧ ∃ x ∈ S, edit x y

/-- The outside target may occur anywhere after the initial vertex. -/
theorem hits_outer_boundary (path : (start :: visits).IsChain edit)
    (inside : start ∈ S) (outside : target ∉ S) (hit : target ∈ visits) :
    ∃ y ∈ visits, OuterBoundary edit S y := by
  induction visits generalizing start with
  | nil => simp at hit
  | cons b rest ih =>
    obtain ⟨step, tail⟩ := List.isChain_cons_cons.mp path
    by_cases hb : b ∈ S
    · have ne : target ≠ b := by
        rintro rfl
        exact outside hb
      obtain ⟨y, hy, boundary⟩ := ih tail hb ((List.mem_cons.mp hit).resolve_left ne)
      exact ⟨y, List.mem_cons_of_mem _ hy, boundary⟩
    · exact ⟨b, by simp, hb, start, inside, step⟩

/-- A cost bound on all outside neighbors certifies a barrier on every such path. -/
theorem hits_cost_at_least [LE β] (score : α → β) (bound : β)
    (certificate : ∀ y, OuterBoundary edit S y → bound ≤ score y)
    (path : (start :: visits).IsChain edit) (inside : start ∈ S)
    (outside : target ∉ S) (hit : target ∈ visits) :
    ∃ y ∈ visits, bound ≤ score y := by
  obtain ⟨y, hy, hb⟩ := hits_outer_boundary path inside outside hit
  exact ⟨y, hy, certificate y hb⟩

end Shellsort.GapEditBarrier
