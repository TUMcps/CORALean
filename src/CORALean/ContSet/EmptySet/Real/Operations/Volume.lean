import CORALean.ContSet.EmptySet.Real.EmptySet
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# `EmptySet.volume`

CORA's `@emptySet/volume_`: `0`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `emptySet/volume_`: `0`. -/
def EmptySet.volume (_ : EmptySet n) : ENNReal := 0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
