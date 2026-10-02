import CORALean.ContSet.Conversion.Float.VPolytope_to_Zonotope
import CORALean.ContSet.Conversion.Float.Zonotope_to_PolyZonotope

/-!
# A hull as a polynomial zonotope, over a floating-point scalar

Through its box's zonotope, whose polynomial-zonotope reading is exact.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

def VPolytope.polyZonotope (P : VPolytope 𝕋 n) : PolyZonotope 𝕋 n :=
  P.zonotope.polyZonotope


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.polyZonotope_contains (P : VPolytope 𝕋 n) :
    P.construct ⊆ P.polyZonotope.construct :=
  subset_trans P.zonotope_contains (Zonotope.polyZonotope_contains _)


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
