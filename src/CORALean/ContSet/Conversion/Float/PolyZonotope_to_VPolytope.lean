import CORALean.ContSet.Conversion.Float.PolyZonotope_to_Zonotope
import CORALean.ContSet.Conversion.Float.Zonotope_to_VPolytope

/-!
# A polynomial zonotope as its corners, over a floating-point scalar

Through the zonotope enclosure and then that zonotope's rounded sign corners.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

def PolyZonotope.vPolytope (pZ : PolyZonotope 𝕋 n) : VPolytope 𝕋 n :=
  pZ.zonotope.vPolytope


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.vPolytope_contains (pZ : PolyZonotope 𝕋 n) :
    pZ.construct ⊆ pZ.vPolytope.construct :=
  subset_trans pZ.zonotope_contains (Zonotope.vPolytope_contains _)


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
