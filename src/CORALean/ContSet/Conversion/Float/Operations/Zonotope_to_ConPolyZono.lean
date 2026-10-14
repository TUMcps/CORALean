module

public import CORALean.ContSet.Conversion.Float.PolyZonotope_to_ConPolyZono
public import CORALean.ContSet.Conversion.Float.Zonotope_to_PolyZonotope

@[expose] public section

/-!
# A zonotope as a constrained polynomial zonotope, over a floating-point scalar — the construction

`Zonotope.conPolyZono` is the construction; `Zonotope_to_ConPolyZono` states and proves what it
guarantees.
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

def Zonotope.conPolyZono (Z : Zonotope (Vec 𝕋 n)) : ConPolyZono 𝕋 (Vec 𝕋 n) :=
  Z.polyZonotope.conPolyZono

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
