module

public import CORALean.ContSet.Conversion.Float.PolyZonotope_to_VPolytope

@[expose] public section

/-!
# A constrained polynomial zonotope as its corners, over a floating-point scalar

Through `ConPolyZono.zonotope`, which drops the constraints, then the zonotope's corners.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

def ConPolyZono.vPolytope (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) : VPolytope (Vec 𝕋 n) :=
  cPZ.zonotope.vPolytope


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.vPolytope_contains (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) :
    cPZ.construct ⊆ cPZ.vPolytope.construct :=
  subset_trans cPZ.zonotope_contains (Zonotope.vPolytope_contains _)


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
