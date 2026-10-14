module

public import CORALean.ContSet.Conversion.Float.PolyZonotope_to_HPolytope

@[expose] public section

/-!
# A constrained polynomial zonotope as halfspaces, over a floating-point scalar — the construction

`ConPolyZono.hPolytope` is the construction; `ConPolyZono_to_HPolytope` states and proves what it
guarantees.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n qI : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.hPolytope (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) (Aq : Mat 𝕋 qI n) : HPolytope
    𝕋 (Vec 𝕋 n) :=
  cPZ.zonotope.hPolytope Aq

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
