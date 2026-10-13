import CORALean.ContSet.SetUnion.Operations.Reduce

/-!
# `SetUnion.reduce` over-approximates the union

Each branch only grows, by `Reduce.reduce_outer`, so a point of some branch
stays a point of that branch reduced, and the union it witnesses in stays
covered after every branch is replaced by its own reduction.
-/

-- Authors:       Claude Sonnet 5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S α : Type} [AddCommGroup α] [Module ℝ α] [ContSet S α] [Reduce S α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem SetUnion.reduce_outer (u : SetUnion S) (o : ℕ) :
    ContSet.construct u ⊆ ContSet.construct (SetUnion.reduce u o) := by
  intro x hx
  obtain ⟨s, hs, hx⟩ := SetUnion.mem_construct.mp hx
  exact SetUnion.mem_construct.mpr
    ⟨Reduce.reduce s o, List.mem_map.mpr ⟨s, hs, rfl⟩, Reduce.reduce_outer s o hx⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
