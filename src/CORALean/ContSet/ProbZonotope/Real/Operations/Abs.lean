import CORALean.ContSet.ProbZonotope.Real.ProbZonotope
import CORALean.ContSet.Zonotope.Real.Operations.Abs

/-!
# `ProbZonotope.abs`

CORA's `abs(probZ)`: `probZ.Z = abs(probZ.Z)`, the entrywise absolute value of the matrix
`[c, G]` of the mean zonotope, centre column included, and the covariance kept. The mean
zonotope becomes `Zonotope.abs` of itself, which is a different set and not an enclosure of the
input; `Theorems.AbsLeCorner` says what it keeps.
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ProbZonotope.abs (P : ProbZonotope n) : ProbZonotope n :=
  { Z := P.Z.abs, cov := P.cov }

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
