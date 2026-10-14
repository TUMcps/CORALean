module

public import CORALean.ContSet.Conversion.Real.ConZonotope_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Zonotope_to_Interval

@[expose] public section

/-!
# A constrained zonotope as a box — the construction

`ConZonotope.interval` is the construction; `ConZonotope_to_Interval` states and proves what it
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

def ConZonotope.interval (cZ : ConZonotope (Vec ℝ n)) : Interval (Vec ℝ n) :=
  cZ.zonotope.interval

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
