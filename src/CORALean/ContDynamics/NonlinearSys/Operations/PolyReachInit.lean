import CORALean.ContDynamics.NonlinearSys.Definitions.PolyReach
import CORALean.ContSet.PolyZonotope.Real.Operations.OfPoint

/-!
# `Alg. 1` line 1: the loop state before the first iteration

`polyReachInit`: [1, Alg. 1] line 1, before the first iteration.

## References

* [1] M. Althoff. "Reachability Analysis of Nonlinear Systems using Conservative
      Polynomialization and Non-Convex Sets". HSCC 2013.
-/

-- Authors:       Claude Sonnet 5
-- Written:       21-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Line 1, before the first iteration. -/
def NonlinearSys.polyReachInit (X₀ : PolyZonotope (Vec ℝ n)) : NonlinearSys.PolyReachState n :=
  { t := 0, R := X₀, Rτ := X₀, Ω := PolyZonotope.ofPoint 0 }    -- 1. t₀,s ← 0; Ω(0) ← {0}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
