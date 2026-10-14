module

public import CORALean.ContSet.Conversion.Float.PolyZonotope_to_ConPolyZono
public import CORALean.ContSet.Conversion.Float.Zonotope_to_PolyZonotope
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_ConPolyZono

@[expose] public section

/-!
# A zonotope as a constrained polynomial zonotope, over a floating-point scalar

Through the polynomial zonotope: nothing rounds at either step.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

variable [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.conPolyZono_contains (Z : Zonotope (Vec 𝕋 n)) :
    Z.construct ⊆ Z.conPolyZono.construct :=
  subset_trans Z.polyZonotope_contains Z.polyZonotope.conPolyZono_contains

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
