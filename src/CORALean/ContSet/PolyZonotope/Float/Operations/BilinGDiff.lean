module

public import CORALean.ContSet.PolyZonotope.Float.Operations.BilinGDown
public import CORALean.ContSet.PolyZonotope.Float.Operations.BilinGUp

@[expose] public section

/-!
# How far a stored `bilin` generator can be from the exact bilinear form

The gap between the generator rounded up and rounded down.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- How far a stored generator can be from the exact bilinear form. -/
def PolyZonotope.bilinGDiff (Q : Fin m → Mat 𝕋 n n) (pZ₁ pZ₂ : PolyZonotope (Vec 𝕋 n)) :
    Mat 𝕋 m ((pZ₁.h + 1) * (pZ₂.h + 1)) :=
  fun k l => subUp (PolyZonotope.bilinGUp Q pZ₁ pZ₂ k l) (PolyZonotope.bilinGDown Q pZ₁ pZ₂ k l)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
