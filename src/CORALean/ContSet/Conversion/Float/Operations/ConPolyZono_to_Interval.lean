module

public import CORALean.ContSet.Conversion.Float.ConPolyZono_to_PolyZonotope
public import CORALean.ContSet.Conversion.Float.PolyZonotope_to_Interval

@[expose] public section

/-!
# A constrained polynomial zonotope as a box, over a floating-point scalar — the construction

`ConPolyZono.interval` is the construction; `ConPolyZono_to_Interval` states and proves what it
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

def ConPolyZono.interval (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) : Interval (Vec 𝕋 n) :=
  cPZ.polyZonotope.interval

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
