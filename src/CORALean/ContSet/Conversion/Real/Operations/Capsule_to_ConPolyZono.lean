module

public import CORALean.ContSet.Conversion.Real.Capsule_to_Interval
public import CORALean.ContSet.Conversion.Real.Interval_to_ConPolyZono

@[expose] public section

/-!
# A capsule as a constrained polynomial zonotope — the construction

`Capsule.conPolyZono` is the construction; `Capsule_to_ConPolyZono` states and proves what it
guarantees.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Capsule.conPolyZono (C : Capsule n) : ConPolyZono (Vec ℝ n) :=
  C.interval.conPolyZono

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
