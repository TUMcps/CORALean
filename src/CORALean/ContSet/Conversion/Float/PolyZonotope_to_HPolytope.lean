import CORALean.ContSet.Conversion.Float.PolyZonotope_to_Zonotope
import CORALean.ContSet.Conversion.Float.Zonotope_to_HPolytope

/-!
# A polynomial zonotope as halfspaces, over a floating-point scalar

Through the zonotope enclosure, then that zonotope's own rounded support bounds; the rows
are the caller's, as in `Zonotope.hPolytope_contains`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n q : ℕ}

def PolyZonotope.hPolytope (pZ : PolyZonotope 𝕋 n) (Aq : Mat 𝕋 q n) : HPolytope 𝕋 n :=
  pZ.zonotope.hPolytope Aq


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.hPolytope_contains (pZ : PolyZonotope 𝕋 n) (Aq : Mat 𝕋 q n) :
    pZ.construct ⊆ (pZ.hPolytope Aq).construct :=
  subset_trans pZ.zonotope_contains (Zonotope.hPolytope_contains _ _)


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
