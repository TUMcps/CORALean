module

public import CORALean.ContSet.EmptySet.Real.EmptySet
public import CORALean.ContSet.VPolytope.Real.Operations.EmptySet

@[expose] public section

/-!
# `EmptySet.vPolytope`

CORA's `@emptySet/polytope`, as the vertex representation: no vertices.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `emptySet/polytope` at vertices: `VPolytope.emptySet`. -/
def EmptySet.vPolytope (_ : EmptySet n) : VPolytope (Vec ℝ n) := VPolytope.emptySet _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
