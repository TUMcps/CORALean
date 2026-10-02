import CORALean.ContSet.MatZonotope.Float.Operations.MatMul
import CORALean.ContSet.MatZonotope.Float.Operations.Point

/-!
# `MatZonotope.matPow`

The exact layer's `Zonotope.matPow` rounded: the identity at order `0`, then
`M · M^k`, recursing on the right as the exact one does so `matPow_outer` unfolds the
same way. The identity is `diagonalBlock fun _ => one`, `𝕋` having no `One` (see
`Interval.matPow`). Each power is materialised, or the next product would rebuild it.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def MatZonotope.matPow (M : MatZonotope 𝕋 n n) : ℕ → MatZonotope 𝕋 n n
  | 0 => MatZonotope.point (diagonalBlock fun _ => one)
  | k + 1 => (MatZonotope.matMul M (MatZonotope.matPow M k)).materialise

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
