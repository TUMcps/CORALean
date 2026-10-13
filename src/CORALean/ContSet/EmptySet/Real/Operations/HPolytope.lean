module

public import CORALean.ContSet.EmptySet.Real.EmptySet
public import CORALean.ContSet.HPolytope.Real.Operations.EmptySet

@[expose] public section

/-!
# `EmptySet.hPolytope`

CORA's `@emptySet/polytope`, as the halfspace representation: the one unsatisfiable row
of `HPolytope.emptySet`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `emptySet/polytope` at halfspaces: `HPolytope.emptySet`. -/
def EmptySet.hPolytope (_ : EmptySet n) : HPolytope (Vec ℝ n) := HPolytope.emptySet _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
