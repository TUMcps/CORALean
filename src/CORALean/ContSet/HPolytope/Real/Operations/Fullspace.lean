import CORALean.ContSet.HPolytope.Real.HPolytope

/-!
# `HPolytope.fullspace`

No constraints at all, so every point qualifies: the unit of `intersection`, and what a
conversion starts from when it has rows to add but none yet.

-/

-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.fullspace (α : Type) [AddCommGroup α] [Module ℝ α] : HPolytope α where
  m := 0
  A := Fin.elim0
  b := Fin.elim0
  me := 0
  Ae := Fin.elim0
  be := Fin.elim0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
