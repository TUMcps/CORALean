import CORALean.ContSet.EmptySet.Real.EmptySet
import CORALean.ContSet.VPolytope.Real.Operations.EmptySet

/-!
# `EmptySet.vPolytope`

CORA's `@emptySet/polytope`, as the vertex representation: no vertices.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `emptySet/polytope` at vertices: `VPolytope.emptySet`. -/
def EmptySet.vPolytope (_ : EmptySet n) : VPolytope (Vec ℝ n) := VPolytope.emptySet _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
