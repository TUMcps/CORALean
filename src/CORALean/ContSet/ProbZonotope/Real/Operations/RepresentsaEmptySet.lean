import CORALean.ContSet.ProbZonotope.Real.ProbZonotope

/-!
# `ProbZonotope.representsaEmptySet`

CORA's `representsa_(probZ, 'emptySet')`: `isempty(probZ.Z) && isempty(probZ.g)`, the empty matrix
pair. The mean zonotope here has a centre, so the answer is always `false`.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ProbZonotope.representsaEmptySet (_ : ProbZonotope n) : Bool := false

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
