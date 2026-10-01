import CORALean.ContSet.SpectraShadow.Real.Operations.Mtimes
import CORALean.ContSet.SpectraShadow.Real.Theorems.MapExact

/-!
# A matrix times a spectrahedral shadow is exact

`map_exact` at `A *ᵥ ·`, the case reachability runs, and with no hypothesis on
`M`: the inequality is not touched, so a singular or non-square matrix keeps the
set exact where a representation stored by its boundary would lose it.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.mtimes_exact {n m : ℕ} (M : Mat ℝ m n) (S : SpectraShadow (Vec ℝ n)) :
    (M *ᵥ ·) '' S.construct = (SpectraShadow.mtimes M S).construct :=
  SpectraShadow.map_exact (Matrix.mulVecLin M) S

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
