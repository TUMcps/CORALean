import CORALean.ContSet.Zonotope.Float.Operations.KeepColumn
import Mathlib.Data.Finset.Sort

/-!
# `Zonotope.compactZeros`, over a floating-point scalar

CORA's `compact_(Z, 'zeros')` at tolerance `0`: the generator columns that are certifiably zero
(`Zonotope.keepColumn`, by the certified `le` in both directions, a proof when it holds) are
dropped; a zero column the test cannot certify is kept, which is sound.
The centre and the error box are copied. Nothing rounds, so the denoted set is the same
(`compactZeros_exact`).
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.compactZeros (Z : Zonotope (Vec 𝕋 n)) : Zonotope (Vec 𝕋 n) where
  h := (Finset.univ.filter fun j => Z.keepColumn j = true).card
  c := Z.c
  G := fun j =>
    Z.G ((Finset.univ.filter fun j => Z.keepColumn j = true).orderEmbOfFin rfl j)
  E := Z.E

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
