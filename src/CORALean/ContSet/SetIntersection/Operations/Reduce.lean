module

public import CORALean.ContSet.SetIntersection.SetIntersection

@[expose] public section

/-!
# `SetIntersection.reduce`

Maps `Reduce.reduce` over every branch, at the same order: an intersection is
only ever enlarged by enlarging what it is an intersection of, so reducing
each branch and re-collecting keeps the shape an intersection already has.

## Inputs
* `I` – intersection
* `o` – order bound

## Output
* every member reduced to order at most `o`
-/

-- Authors:       Claude Sonnet 5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S α : Type} [AddCommGroup α] [Module ℝ α] [ContSet S α] [Reduce S α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every branch, reduced to at most `o` of whatever it counts. -/
def SetIntersection.reduce (I : SetIntersection S) (o : ℕ) : SetIntersection S :=
  ⟨I.sets.map fun s => Reduce.reduce s o⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
