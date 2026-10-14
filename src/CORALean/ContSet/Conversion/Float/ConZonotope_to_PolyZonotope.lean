module

public import CORALean.ContSet.Conversion.Float.ConZonotope_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Zonotope_to_PolyZonotope
public import CORALean.ContSet.Conversion.Float.Operations.ConZonotope_to_PolyZonotope

@[expose] public section

/-!
# A constrained zonotope as a polynomial zonotope, over a floating-point scalar

Through the zonotope, dropping the constraints: nothing rounds at either step.
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

theorem ConZonotope.polyZonotope_contains (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) :
    cZ.construct ⊆ cZ.polyZonotope.construct :=
  subset_trans cZ.zonotope_contains cZ.zonotope.polyZonotope_contains

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
