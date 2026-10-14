module

public import CORALean.ContSet.Conversion.Real.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Zonotope_to_Ellipsoid

@[expose] public section

/-!
# A box as an ellipsoid — the construction

`Interval.ellipsoid` is the construction; `Interval_to_Ellipsoid` states and proves what it
guarantees.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Interval.ellipsoid (I : Interval (Vec ℝ n)) : Ellipsoid n :=
  I.zonotope.ellipsoid

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
