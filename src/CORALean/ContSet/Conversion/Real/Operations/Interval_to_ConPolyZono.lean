module

public import CORALean.ContSet.Conversion.Real.Interval_to_PolyZonotope
public import CORALean.ContSet.Conversion.Real.PolyZonotope_to_ConPolyZono

@[expose] public section

/-!
# A box as a constrained polynomial zonotope — the construction

`Interval.conPolyZono` is the construction; `Interval_to_ConPolyZono` states and proves what it
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

noncomputable def Interval.conPolyZono (I : Interval (Vec ℝ n)) : ConPolyZono (Vec ℝ n) :=
  I.polyZonotope.conPolyZono

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
