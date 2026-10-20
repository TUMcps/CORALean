module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Compact

@[expose] public section

/-!
# How large `compact`'s result is

Bounds and not counts: how many columns survive a merge depends on how many were equal, which
nothing in the operand's *sizes* fixes. What holds at every operand is that compaction never
grows anything: it keeps a sub-`Finset` of the columns and of the factors, and leaves the
independent block alone. `Complexity/Time/Reduce.lean` needs that to price the ranking at the
operand's own counts, an upper bound because compaction cannot have made them larger.

## Inputs
* `pZ` – polynomial zonotope

## Hypotheses
* none

## Conclusion
* compacting does not add generators
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The kept columns are a sub-`Finset` of all of them, so there are no more. -/
theorem PolyZonotope.compact_h_le (pZ : PolyZonotope α) : pZ.compact.h ≤ pZ.h := by
  have h := Finset.card_le_univ (PolyZonotope.compactKeep pZ.E pZ.G)
  rw [Fintype.card_fin] at h
  exact h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
