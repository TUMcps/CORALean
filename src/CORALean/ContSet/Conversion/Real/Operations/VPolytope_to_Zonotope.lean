module

public import CORALean.ContSet.Conversion.Real.VPolytope_to_Interval
public import CORALean.ContSet.Conversion.Real.Interval_to_Zonotope

@[expose] public section

/-!
# A hull as a zonotope — the construction

`VPolytope.zonotope` is the construction; `VPolytope_to_Zonotope` states and proves what it
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

noncomputable def VPolytope.zonotope (P : VPolytope (Vec ℝ n)) : Zonotope (Vec ℝ n) :=
  P.interval.zonotope

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
