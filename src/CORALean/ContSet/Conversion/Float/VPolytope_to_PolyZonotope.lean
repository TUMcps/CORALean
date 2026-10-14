module

public import CORALean.ContSet.Conversion.Float.VPolytope_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Zonotope_to_PolyZonotope
public import CORALean.ContSet.Conversion.Float.Operations.VPolytope_to_PolyZonotope

@[expose] public section

/-!
# A hull as a polynomial zonotope, over a floating-point scalar

Through its box's zonotope, whose polynomial-zonotope reading is exact.
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

theorem VPolytope.polyZonotope_contains (P : VPolytope (Vec 𝕋 n)) :
    P.construct ⊆ P.polyZonotope.construct :=
  subset_trans P.zonotope_contains (Zonotope.polyZonotope_contains _)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
