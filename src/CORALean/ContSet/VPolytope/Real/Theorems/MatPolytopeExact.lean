import CORALean.ContSet.VPolytope.Real.Operations.MatPolytope
import CORALean.ContSet.VPolytope.Real.Theorems.MapExact

/-!
# The matrix polytope of a vertex list is its columns, exactly

The matrices of `matPolytope P` are exactly the vectors of `P` read as columns.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.matPolytope_exact (P : VPolytope (Vec ℝ n)) :
    (fun v => (fun i _ => v i : Mat ℝ n 1)) '' P.construct = P.matPolytope.construct :=
  VPolytope.map_exact (colLin n) P

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
