import CORALean.ContSet.Zonotope.Float.Operations.MatMul
import CORALean.ContSet.Zonotope.Float.Operations.PointMat

/-!
# `GZonotope.matPow`

The exact layer's `Zonotope.matPow` rounded: the identity at order `0`, then
`M · M^k`, recursing on the right as the exact one does so `matPow_outer` unfolds the
same way. The identity is `diagonalBlock fun _ => one`, `𝕋` having no `One` (see
`Interval.matPow`). Each power is materialised, or the next product would rebuild it.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   09-October-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def GZonotope.matPow (M : GZonotope (Mat 𝕋 n n)) : ℕ → GZonotope (Mat 𝕋 n n)
  | 0 => GZonotope.pointMat (diagonalBlock fun _ => one)
  | k + 1 => (GZonotope.matMul M (GZonotope.matPow M k)).materialiseMat

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
