import CORALean.ContSet.Interval.Real.Interval
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# `Interval.volume`

CORA's `@interval/volume_`: the product of the widths. `ENNReal.ofReal` clips a negative width
to `0`, so a crossed box, which denotes `∅`, has volume `0` with no case split.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `interval/volume_`: `∏ᵢ (sup i - inf i)`, a crossed coordinate counting as `0`. -/
noncomputable def Interval.volume (I : Interval (Vec ℝ n)) : ENNReal :=
  ∏ i, ENNReal.ofReal (I.sup i - I.inf i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
