import CORALean.ContSet.ZonoBundle.Real.Operations.Map
import CORALean.ContSet.Zonotope.Real.Operations.Project

/-!
# `ZonoBundle.project`

CORA's `@zonoBundle/project`: every member zonotope projected on its own,
`zB.Z{i} = project(zB.Z{i},dims)`. `dims` may repeat or reorder coordinates. Reading coordinates
is linear, so this is `map` at the selection map, member by member.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ZonoBundle.project (zB : ZonoBundle (Vec ℝ n)) (dims : Fin m → Fin n) :
    ZonoBundle (Vec ℝ m) :=
  zB.map (LinearMap.funLeft ℝ ℝ dims)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
