module

public import CORALean.ContSet.Zonotope.Float.Zonotope
public import Mathlib.Data.Finset.Sort

@[expose] public section

/-!
# `Zonotope.compactZeros`, over a floating-point scalar

CORA's `compact_(Z, 'zeros')` at tolerance `0`: the generator columns that are certifiably zero
(`Zonotope.aux_keepColumn`, by the certified `le` in both directions, a proof when it holds) are
dropped; a zero column the test cannot certify is kept, which is sound.
The center and the error box are copied. Nothing rounds, so the denoted set is the same
(`compactZeros_exact`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Whether column `j` is not certified zero. -/
def Zonotope.aux_keepColumn (Z : Zonotope (Vec 𝕋 n)) (j : Fin Z.h) : Bool :=
  !(List.finRange n).all fun i => le (Z.G j i) zero && le zero (Z.G j i)


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.compactZeros (Z : Zonotope (Vec 𝕋 n)) : Zonotope (Vec 𝕋 n) where
  h := (Finset.univ.filter fun j => Z.aux_keepColumn j = true).card
  c := Z.c
  G := fun j =>
    Z.G ((Finset.univ.filter fun j => Z.aux_keepColumn j = true).orderEmbOfFin rfl j)
  I_error := Z.I_error

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
