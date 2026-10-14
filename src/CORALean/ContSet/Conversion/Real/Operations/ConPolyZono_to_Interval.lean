module

public import CORALean.ContSet.Conversion.Real.ConPolyZono_to_PolyZonotope
public import CORALean.ContSet.Conversion.Real.PolyZonotope_to_Interval

@[expose] public section

/-!
# A constrained polynomial zonotope as a box — the construction

`ConPolyZono.interval` is the construction; `ConPolyZono_to_Interval` states and proves what it
guarantees.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.interval (cPZ : ConPolyZono (Vec ℝ n)) : Interval (Vec ℝ n) :=
  cPZ.polyZonotope.interval

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
