import CORALean.ContSet.Fullspace.Real.Fullspace
import CORALean.ContSet.HPolytope.Real.Operations.Fullspace

/-!
# `Fullspace.hPolytope`

CORA's `@fullspace/polytope`, which is `polytope.Inf(n)`: no rows at all
(`HPolytope.fullspace`). CORA throws at `n = 0`; nothing here does.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `fullspace/polytope`: `HPolytope.fullspace`. -/
def Fullspace.hPolytope (_ : Fullspace n) : HPolytope (Vec ℝ n) := HPolytope.fullspace _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
