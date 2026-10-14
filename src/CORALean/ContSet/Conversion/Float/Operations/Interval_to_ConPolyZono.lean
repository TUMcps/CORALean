module

public import CORALean.ContSet.Conversion.Float.Interval_to_PolyZonotope
public import CORALean.ContSet.Conversion.Float.PolyZonotope_to_ConPolyZono

@[expose] public section

/-!
# A box as a constrained polynomial zonotope, over a floating-point scalar — the construction

`Interval.conPolyZono` is the construction; `Interval_to_ConPolyZono` states and proves what it
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

def Interval.conPolyZono (I : Interval (Vec 𝕋 n)) : ConPolyZono 𝕋 (Vec 𝕋 n) :=
  I.polyZonotope.conPolyZono

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
