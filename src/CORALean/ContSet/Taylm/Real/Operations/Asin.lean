import CORALean.ContSet.Taylm.Real.Operations.Taylor
import CORALean.ContSet.Taylm.Real.Operations.ConstCoef
import CORALean.ContSet.Taylm.Real.Operations.Mag
import CORALean.Global.ElementaryDerivBounds

/-!
# `Taylm.asin`

CORA's `asin`: the expansion at the constant part. `asin⁽ᴺ⁺¹⁾ x` is `asinPoly N x` times
`(1 - x²)⁻⁽²ᴺ⁺¹⁾ᐟ²`, bounded by `asinDom N` at the magnitude `m` and `(1 - m²)⁻⁽²ᴺ⁺¹⁾ᐟ²`,
finite below one, the domain `AsinOuter` assumes.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.asin (T : Taylm n) : Taylm n :=
  T.taylor Real.arcsin T.constCoef
    ((asinDom T.maxOrder).eval T.mag * ((√(1 - T.mag ^ 2))⁻¹) ^ (2 * T.maxOrder + 1))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
