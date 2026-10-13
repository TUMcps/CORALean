module

public import CORALean.ContSet.SpectraShadow.Real.Operations.Mtimes
public import CORALean.ContSet.SpectraShadow.Real.Theorems.MapExact

@[expose] public section

/-!
# A matrix times a spectrahedral shadow is exact

`map_exact` at `A *ᵥ ·`, the case reachability runs, and with no hypothesis on
`M`: the inequality is not touched, so a singular or non-square matrix keeps the
set exact where a representation stored by its boundary would lose it.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.mtimes_exact {n m : ℕ} (M : Mat ℝ m n) (S : SpectraShadow (Vec ℝ n)) :
    (M *ᵥ ·) '' S.construct = (SpectraShadow.mtimes M S).construct :=
  SpectraShadow.map_exact (Matrix.mulVecLin M) S

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
