module

public import CORALean.ContSet.Conversion.Real.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Zonotope_to_ConZonotope

@[expose] public section

/-!
# A box as a constrained zonotope — the construction

`Interval.conZonotope` is the construction; `Interval_to_ConZonotope` states and proves what it
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

noncomputable def Interval.conZonotope (I : Interval (Vec ℝ n)) : ConZonotope (Vec ℝ n) :=
  I.zonotope.conZonotope

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
