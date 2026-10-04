import CORALean.ContSet.VPolytope.Real.Operations.ColLin
import CORALean.ContSet.VPolytope.Real.Operations.Map

/-!
# `VPolytope.matPolytope`

CORA's `matPolytope(P)`: each vertex `v` of the polytope read as the `n × 1` matrix with that
column, the matrix polytope of those. A vertex list is mapped by the linear embedding of a vector
as a column.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def VPolytope.matPolytope (P : VPolytope (Vec ℝ n)) : VPolytope (Mat ℝ n 1) :=
  P.map (colLin n)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
