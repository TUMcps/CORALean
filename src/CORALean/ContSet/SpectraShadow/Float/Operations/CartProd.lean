import CORALean.ContSet.SpectraShadow.Float.Operations.PadLeft
import CORALean.ContSet.SpectraShadow.Float.Operations.PadRight
import CORALean.ContSet.SpectraShadow.Float.Operations.Plus

/-!
# `SpectraShadow.cartProd`

CORA's `@spectraShadow/cartProd_`, as the exact layer has it: each shadow is put into its own
coordinates of the product, zero in the other's, and the two are added. The padding stores
exact zeros, so the only rounding is `plus`'s on the centre, where one summand is zero.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def SpectraShadow.cartProd (S : SpectraShadow 𝕋 (Vec 𝕋 n)) (T : SpectraShadow 𝕋 (Vec 𝕋 m)) :
    SpectraShadow 𝕋 (Vec 𝕋 (n + m)) :=
  let left := S.padLeft m
  let right := T.padRight n
  left.plus right

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
