import CORALean.ContSet.Conversion.Float.VPolytope_to_PolyZonotope
import CORALean.ContSet.Conversion.Float.PolyZonotope_to_ConPolyZono

/-!
# A hull as a constrained polynomial zonotope, over a floating-point scalar

Through the polynomial zonotope; the constraint-free embedding is exact.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

def VPolytope.conPolyZono (P : VPolytope 𝕋 n) : ConPolyZono 𝕋 n :=
  P.polyZonotope.conPolyZono


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.conPolyZono_contains (P : VPolytope 𝕋 n) :
    P.construct ⊆ P.conPolyZono.construct :=
  subset_trans P.polyZonotope_contains P.polyZonotope.conPolyZono_contains


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
