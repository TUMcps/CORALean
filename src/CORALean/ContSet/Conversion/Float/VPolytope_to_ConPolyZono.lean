module

public import CORALean.ContSet.Conversion.Float.VPolytope_to_PolyZonotope
public import CORALean.ContSet.Conversion.Float.PolyZonotope_to_ConPolyZono
public import CORALean.ContSet.Conversion.Float.Operations.VPolytope_to_ConPolyZono

@[expose] public section

/-!
# A hull as a constrained polynomial zonotope, over a floating-point scalar

Through the polynomial zonotope; the constraint-free embedding is exact.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.conPolyZono_contains (P : VPolytope (Vec 𝕋 n)) :
    P.construct ⊆ P.conPolyZono.construct :=
  subset_trans P.polyZonotope_contains P.polyZonotope.conPolyZono_contains

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
