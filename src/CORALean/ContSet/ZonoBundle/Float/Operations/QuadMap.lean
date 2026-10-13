import CORALean.ContSet.ZonoBundle.Float.ZonoBundle
import CORALean.ContSet.Zonotope.Float.Operations.QuadMap

/-!
# `ZonoBundle.quadMap`, over a floating-point scalar

CORA's `zonoBundle`/`quadMap(zB, Q)`: every member is replaced by its zonotope quadratic map,
the count unchanged.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ZonoBundle.quadMap (Q : Fin m → Mat 𝕋 n n) (zB : ZonoBundle (Vec 𝕋 n)) :
    ZonoBundle (Vec 𝕋 m) where
  k := zB.k
  Z := fun i => Zonotope.quadMap Q (zB.Z i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
