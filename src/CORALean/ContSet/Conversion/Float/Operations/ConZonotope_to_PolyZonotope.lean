module

public import CORALean.ContSet.Conversion.Float.ConZonotope_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Zonotope_to_PolyZonotope

@[expose] public section

/-!
# A constrained zonotope as a polynomial zonotope, over a floating-point scalar — the construction

`ConZonotope.polyZonotope` is the construction; `ConZonotope_to_PolyZonotope` states and proves what
it guarantees.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConZonotope.polyZonotope (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) : PolyZonotope (Vec 𝕋 n) :=
  cZ.zonotope.polyZonotope

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
