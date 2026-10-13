import CORALean.ContSet.ProbZonotope.Real.ProbZonotope

/-!
# `ProbZonotope.mean`

CORA's `mean`: the zonotope of possible means, `Z` itself. `Theorems.MeanExact` says it is
exactly the set of the laws' expectations.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ProbZonotope.mean (P : ProbZonotope n) : Zonotope (Vec ℝ n) := P.Z

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
