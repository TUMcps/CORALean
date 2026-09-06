import CORALean.ContSet.VPolytope.Real.Operations.Mtimes
import CORALean.ContSet.VPolytope.Real.Operations.MtimesEqMap
import CORALean.ContSet.VPolytope.Real.Theorems.MapExact

/-!
# A matrix times a vertex description is exact

`map_exact` at `A *ᵥ ·`, once `mtimes` is known to be that map. The float layer
refines this one, paying its rounding into an error box around the mapped
vertices.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   04-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.mtimes_exact {n m : ℕ} (M : Mat ℝ m n) (P : VPolytope (Vec ℝ n)) :
    (M *ᵥ ·) '' P.construct = (VPolytope.mtimes M P).construct := by
  rw [VPolytope.mtimes_eq_map]
  exact VPolytope.map_exact (Matrix.mulVecLin M) P

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
