import CORALean.ContSet.ZonoBundle.Float.ZonoBundle
import CORALean.ContSet.Zonotope.Float.Operations.Project

/-!
# `ZonoBundle.project` over a floating-point scalar

The same `k`, each member projected on its own with `Zonotope.project`: selecting coordinates
moves stored floats without arithmetic, so nothing rounds. `dims` may repeat or reorder
coordinates.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ZonoBundle.project (zB : ZonoBundle 𝕋 n) (dims : Fin m → Fin n) : ZonoBundle 𝕋 m where
  k := zB.k
  Z := fun i => Zonotope.project (zB.Z i) dims

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
