module

public import CORALean.ContSet.Interval.Real.Interval
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

/-!
# `Interval.matVolume`

CORA's `@intervalMatrix/volume`: the volume of `interval(intMat)`, the product of all entry widths.
`ENNReal.ofReal` clips a negative width to `0`, so a crossed box, which denotes `∅`, has volume
`0`. CORA also answers `0` for a matrix with no entries, where the empty product here is `1`,
the Lebesgue measure of the one point of `ℝ⁰`; this is `Interval.volume`'s convention at `n = 0`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `volume(intMat)`: `∏ᵢⱼ (sup i j - inf i j)`, a crossed entry counting as `0`. -/
noncomputable def Interval.matVolume (A : Interval (Mat ℝ m n)) : ENNReal :=
  ∏ i, ∏ j, ENNReal.ofReal (A.sup i j - A.inf i j)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
