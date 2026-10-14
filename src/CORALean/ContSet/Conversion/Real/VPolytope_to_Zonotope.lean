module

public import CORALean.ContSet.Conversion.Real.VPolytope_to_Interval
public import CORALean.ContSet.Conversion.Real.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.VPolytope_to_Zonotope

@[expose] public section

/-!
# A hull as a zonotope

Through its box. A tighter zonotope enclosure of a vertex list is a fitting
problem rather than a conversion, so the box is what a definition can give.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.zonotope_contains (P : VPolytope (Vec ℝ n)) :
    P.construct ⊆ P.zonotope.construct :=
  subset_trans P.interval_contains (Interval.zonotope_contains _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
