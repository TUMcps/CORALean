import CORALean.ContSet.HPolytope.Real.Operations.Translate

/-!
# `HPolytope.minus`

CORA's `polytope/minus.m` accepts a column vector as subtrahend and nothing else
(a set subtrahend is a Minkowski difference, a different method), so `minus P v`
is the translation by `-v`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.minus (P : HPolytope α) (v : α) : HPolytope α :=
  HPolytope.translate (-v) P

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
