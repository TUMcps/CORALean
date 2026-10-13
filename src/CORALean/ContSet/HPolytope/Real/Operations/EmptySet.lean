import CORALean.ContSet.HPolytope.Real.HPolytope

/-!
# `HPolytope.emptySet`

One unsatisfiable row, `0 ≤ -1`: the absorbing element of `intersection`, and what a
halfspace description says when it has nothing.

Stated with a row rather than with no points at all, because a representation
has to denote `∅` by data a machine can hold.
-/

-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.emptySet (α : Type) [AddCommGroup α] [Module ℝ α] : HPolytope α where
  m := 1
  A := fun _ => 0
  b := fun _ => -1
  me := 0
  Ae := Fin.elim0
  be := Fin.elim0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
