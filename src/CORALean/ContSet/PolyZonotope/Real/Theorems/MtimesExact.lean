import CORALean.ContSet.PolyZonotope.Real.Operations.Mtimes
import CORALean.ContSet.PolyZonotope.Real.Theorems.MapExact

/-!
# A matrix times a polynomial zonotope is exact

`map_exact` at `A *ᵥ ·`, which is the case reachability runs. The exponent
matrix never enters: the monomials are scalars, so a linear map of the ambient
space cannot touch them.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   04-September-2026
-- Last revision: ---

namespace CORALean.Real

open Matrix

theorem PolyZonotope.mtimes_exact {n m : ℕ} (M : Mat ℝ m n) (PZ : PolyZonotope (Vec ℝ n)) :
    (M *ᵥ ·) '' PZ.construct = (PolyZonotope.mtimes M PZ).construct :=
  PolyZonotope.map_exact (Matrix.mulVecLin M) PZ

end CORALean.Real
