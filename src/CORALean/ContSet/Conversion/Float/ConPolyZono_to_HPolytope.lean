module

public import CORALean.ContSet.Conversion.Float.PolyZonotope_to_HPolytope
public import CORALean.ContSet.Conversion.Float.Operations.ConPolyZono_to_HPolytope

@[expose] public section

/-!
# A constrained polynomial zonotope as halfspaces, over a floating-point scalar

Through `ConPolyZono.zonotope`, which drops the constraints, then the zonotope's halfspaces.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n qI : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.hPolytope_contains (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) (Aq : Mat 𝕋 qI n) :
    cPZ.construct ⊆ (cPZ.hPolytope Aq).construct :=
  subset_trans cPZ.zonotope_contains (Zonotope.hPolytope_contains _ _)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
