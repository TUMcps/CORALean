module

public import CORALean.ContSet.Conversion.Float.ConZonotope_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Zonotope_to_HPolytope

@[expose] public section

/-!
# A constrained zonotope as halfspaces, over a floating-point scalar — the construction

`ConZonotope.hPolytope` is the construction; `ConZonotope_to_HPolytope` states and proves what it
guarantees.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n q : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConZonotope.hPolytope (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) (Aq : Mat 𝕋 q n) : HPolytope 𝕋 (Vec 𝕋 n) :=
  cZ.zonotope.hPolytope Aq

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
