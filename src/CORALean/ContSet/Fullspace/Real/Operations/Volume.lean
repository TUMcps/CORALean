module

public import CORALean.ContSet.Fullspace.Real.Fullspace
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

/-!
# `Fullspace.volume`

CORA's `@fullspace/volume_`: `Inf`. CORA answers `NaN` at `n = 0`, which is not a value
of `ENNReal`, so the guarantee is stated for `0 < n` only.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `fullspace/volume_`: `Inf`, for `0 < n`. -/
def Fullspace.volume (_ : Fullspace n) : ENNReal := ⊤

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
