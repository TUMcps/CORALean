import CORALean.ContSet.Zonotope.Float.Operations.CubFoldUp

/-!
# `Zonotope.cubMapCUp`

The centre of `Zonotope.cubMap` on the stored floats, rounded up: the coefficient of the constant
monomial `(0, 0, 0)`, plus half the sum of the pure squares `β_y²` of `listQuad{1}` (`β² = 0.5 +
0.5 (2β² - 1)`). Halving rounds nothing.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.cubMapCUp (T : Fin m → Fin n → Mat 𝕋 n n) (Z : Zonotope (Vec 𝕋 n)) : Vec 𝕋 m :=
  fun i => addUp (Zonotope.cubFoldUp T Z i 0 0 0)
    (half (sumUp fun y : Fin Z.h => Zonotope.cubFoldUp T Z i 0 y.succ y.succ))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
