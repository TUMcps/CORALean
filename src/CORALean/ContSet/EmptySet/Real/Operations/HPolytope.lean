import CORALean.ContSet.EmptySet.Real.EmptySet
import CORALean.ContSet.HPolytope.Real.Operations.EmptySet

/-!
# `EmptySet.hPolytope`

CORA's `@emptySet/polytope`, as the halfspace representation: the one unsatisfiable row
of `HPolytope.emptySet`.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `emptySet/polytope` at halfspaces: `HPolytope.emptySet`. -/
def EmptySet.hPolytope (_ : EmptySet n) : HPolytope (Vec ℝ n) := HPolytope.emptySet _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
