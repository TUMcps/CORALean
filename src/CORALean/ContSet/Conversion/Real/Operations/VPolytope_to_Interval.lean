module

public import CORALean.ContSet.VPolytope.Real.Operations.SupportBound
public import CORALean.ContSet.Interval.Real.Interval

@[expose] public section

/-!
# A hull as a box — the construction

`VPolytope.interval` is the construction; `VPolytope_to_Interval` states and proves what it
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

noncomputable def VPolytope.interval (P : VPolytope (Vec ℝ n)) : Interval (Vec ℝ n) where
  inf := fun i => ⨅ l, P.V l i
  sup := fun i => ⨆ l, P.V l i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
