module

public import CORALean.ContSet.Fullspace.Real.Fullspace
public import CORALean.ContSet.HPolytope.Real.Operations.Fullspace

@[expose] public section

/-!
# `Fullspace.hPolytope`

CORA's `@fullspace/polytope`, which is `polytope.Inf(n)`: no rows at all
(`HPolytope.fullspace`). CORA throws at `n = 0`; nothing here does.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `fullspace/polytope`: `HPolytope.fullspace`. -/
def Fullspace.hPolytope (_ : Fullspace n) : HPolytope (Vec ℝ n) := HPolytope.fullspace _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
