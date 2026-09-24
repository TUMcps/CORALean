import CORALean.ContSet.SetIntersection.SetIntersection

/-!
# `SetIntersection.reduce`

Maps `Reduce.reduce` over every branch, at the same order: an intersection is
only ever enlarged by enlarging what it is an intersection of, so reducing
each branch and re-collecting keeps the shape an intersection already has.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S α : Type} [AddCommGroup α] [Module ℝ α] [ContSet S α] [Reduce S α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every branch, reduced to at most `o` of whatever it counts. -/
def SetIntersection.reduce (I : SetIntersection S) (o : ℕ) : SetIntersection S :=
  ⟨I.sets.map fun s => Reduce.reduce s o⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
