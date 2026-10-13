import CORALean.ContSet.Zonotope.Real.Operations.Map
import Mathlib.Algebra.Module.Equiv.Basic

/-!
# `Zonotope.project`

CORA's `@zonotope/project`: the centre and every generator at the chosen coordinates. `dims` may
repeat or reorder coordinates. Reading coordinates is linear, so this is `map` at the selection
map, and `project_exact` is `map_exact`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.project (Z : Zonotope (Vec ℝ n)) (dims : Fin m → Fin n) : Zonotope (Vec ℝ m) :=
  Z.map (LinearMap.funLeft ℝ ℝ dims)


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
