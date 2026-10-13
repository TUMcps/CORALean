import CORALean.ContSet.ZonoBundle.Float.ZonoBundle
import CORALean.ContSet.Zonotope.Float.Operations.MtimesIntervalMat

/-!
# `ZonoBundle.mtimesIntervalMat`

`ZonoBundle.mtimes` at a float interval matrix: the same `k`, each member multiplied on its
own by `Zonotope.mtimesIntervalMat`, so what the matrix's width costs lands in that member's
generators and never in a bundle-wide box. This is what a step against an enclosure of
`e^{Ar}` multiplies a bundle by.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ZonoBundle.mtimesIntervalMat (IM : Interval (Mat 𝕋 m n)) (zB : ZonoBundle (Vec 𝕋 n)) :
    ZonoBundle (Vec 𝕋 m) where
  k := zB.k
  Z := fun i => Zonotope.mtimesIntervalMat IM (zB.Z i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
