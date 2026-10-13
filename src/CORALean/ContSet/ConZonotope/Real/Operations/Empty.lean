module

public import CORALean.ContSet.ConZonotope.Real.ConZonotope
public import CORALean.ContSet.HPolytope.Real.Operations.EmptySet

@[expose] public section

/-!
# `ConZonotope.empty`

CORA's `conZonotope.empty(n)`: no generators, and the unsatisfiable row `0 ≤ -1` on the (empty)
coefficient vector, so no coefficient vector is admitted.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `conZonotope.empty(n)`: the centre `0`, no generators, and `HPolytope.emptySet` as
constraint. -/
def ConZonotope.empty (n : ℕ) : ConZonotope (Vec ℝ n) :=
  ⟨0, 0, Fin.elim0, HPolytope.emptySet _⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
