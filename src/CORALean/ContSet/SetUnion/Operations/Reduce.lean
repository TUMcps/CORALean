import CORALean.ContSet.SetUnion.SetUnion

/-!
# `SetUnion.reduce`

Maps `Reduce.reduce` over every branch, at the same order: a union is only
ever enlarged by enlarging what it is a union of, so reducing each branch and
re-collecting keeps the shape a union already has.
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
def SetUnion.reduce (u : SetUnion S) (o : ℕ) : SetUnion S :=
  ⟨u.sets.map fun s => Reduce.reduce s o⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
