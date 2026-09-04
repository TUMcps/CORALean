import CORALean.ContSet.ConZonotope.Real.Operations.Mtimes
import CORALean.ContSet.ConZonotope.Real.Theorems.MapExact

/-!
# A matrix times a constrained zonotope is exact

`map_exact` at `A *ᵥ ·`, which is the case reachability runs: the constraints
are on the coefficients and a linear map of the ambient space never sees them.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   04-September-2026
-- Last revision: ---

namespace CORALean.Real

open Matrix

theorem ConZonotope.mtimes_exact {n m : ℕ} (M : Mat ℝ m n) (C : ConZonotope (Vec ℝ n)) :
    (M *ᵥ ·) '' C.construct = (ConZonotope.mtimes M C).construct :=
  ConZonotope.map_exact (Matrix.mulVecLin M) C

end CORALean.Real
