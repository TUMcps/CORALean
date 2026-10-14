module

public import CORALean.ContSet.Conversion.Real.Capsule_to_Interval
public import CORALean.ContSet.Conversion.Real.Interval_to_Ellipsoid

@[expose] public section

/-!
# A capsule as an ellipsoid — the construction

`Capsule.ellipsoid` is the construction; `Capsule_to_Ellipsoid` states and proves what it
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

noncomputable def Capsule.ellipsoid (C : Capsule n) : Ellipsoid n :=
  C.interval.ellipsoid

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
