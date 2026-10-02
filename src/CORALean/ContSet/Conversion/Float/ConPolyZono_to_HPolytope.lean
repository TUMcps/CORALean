import CORALean.ContSet.Conversion.Float.PolyZonotope_to_HPolytope

/-!
# A constrained polynomial zonotope as halfspaces, over a floating-point scalar

Through `ConPolyZono.zonotope`, which drops the constraints, then the zonotope's halfspaces.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n q : ℕ}

def ConPolyZono.hPolytope (cPZ : ConPolyZono 𝕋 n) (Aq : Mat 𝕋 q n) : HPolytope 𝕋 n :=
  cPZ.zonotope.hPolytope Aq


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.hPolytope_contains (cPZ : ConPolyZono 𝕋 n) (Aq : Mat 𝕋 q n) :
    cPZ.construct ⊆ (cPZ.hPolytope Aq).construct :=
  subset_trans cPZ.zonotope_contains (Zonotope.hPolytope_contains _ _)


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
