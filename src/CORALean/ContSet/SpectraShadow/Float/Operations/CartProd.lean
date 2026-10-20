module

public import CORALean.ContSet.SpectraShadow.Float.Operations.PadLeft
public import CORALean.ContSet.SpectraShadow.Float.Operations.PadRight
public import CORALean.ContSet.SpectraShadow.Float.Operations.Plus

@[expose] public section

/-!
# `SpectraShadow.cartProd`

CORA's `@spectraShadow/cartProd_`, as the exact layer has it: each shadow is put into its own
coordinates of the product, zero in the other's, and the two are added. The padding stores
exact zeros, so the only rounding is `plus`'s on the center, where one summand is zero.

## Inputs
* `S` – spectrahedral shadow
* `T` – spectrahedral shadow

## Output
* the Cartesian product, `S` and `T` padded with zeros and added
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


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
