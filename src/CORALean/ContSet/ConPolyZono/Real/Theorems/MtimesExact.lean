import CORALean.ContSet.ConPolyZono.Real.Operations.Mtimes
import CORALean.ContSet.ConPolyZono.Real.Theorems.MapExact

/-!
# A matrix times a constrained polynomial zonotope is exact

`map_exact` at `A *ᵥ ·`, which is the case reachability runs. The constraint is
on the factors, and a linear map of the ambient space moves points, not factors.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   04-September-2026
-- Last revision: ---

namespace CORALean.Real

open Matrix

theorem ConPolyZono.mtimes_exact {k n : ℕ} (M : Mat ℝ k n) (C : ConPolyZono (Vec ℝ n)) :
    (M *ᵥ ·) '' C.construct = (ConPolyZono.mtimes M C).construct :=
  ConPolyZono.map_exact (Matrix.mulVecLin M) C

end CORALean.Real
