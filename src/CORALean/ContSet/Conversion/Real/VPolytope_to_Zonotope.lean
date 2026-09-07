import CORALean.ContSet.Conversion.Real.VPolytope_to_Interval
import CORALean.ContSet.Conversion.Real.Interval_to_Zonotope

/-!
# A hull as a zonotope

Through its box. A tighter zonotope enclosure of a vertex list is a fitting
problem rather than a conversion, so the box is what a definition can give.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}

noncomputable def VPolytope.zonotope (P : VPolytope (Vec ℝ n)) : Zonotope (Vec ℝ n) :=
  P.interval.zonotope


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.zonotope_contains (P : VPolytope (Vec ℝ n)) :
    P.construct ⊆ P.zonotope.construct :=
  subset_trans P.interval_contains (Interval.zonotope_contains _)


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
