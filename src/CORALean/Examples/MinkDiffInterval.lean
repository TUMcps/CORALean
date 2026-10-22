import CORALean.ContSet.Interval.Real.Theorems.MinkDiffExact

/-!
# The Minkowski difference of two boxes is exact

`MinkDiff`'s obligation is *inner*: an implementation may only ever return less than the true
difference, never more. `Interval.minkDiff` meets it with nothing to spare — it is exact
(`minkDiff_exact`). A box of half-width `0.2` taken from a box of half-width `1` is the box of
half-width `0.8`: `0.5` sits inside it, and `0.9` outside, cheaply, since the representation
itself already excludes it.

## Inputs
* none

## Output
* first example box
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       07-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

def MDiff.I1 : Interval (Vec ℝ 1) := ⟨![(-1:ℝ)], ![(1:ℝ)]⟩
/-- The box `[-0.2, 0.2]`. -/
def MDiff.I2 : Interval (Vec ℝ 1) := ⟨![(-0.2:ℝ)], ![(0.2:ℝ)]⟩

/-- The box `[-0.2, 0.2]` is nonempty. -/
theorem MDiff.I2_nonempty : MDiff.I2.IsNonempty := by
  intro i
  fin_cases i
  show MDiff.I2.inf 0 ≤ MDiff.I2.sup 0
  norm_num [MDiff.I2]

/-- The exact difference is `[-0.8, 0.8]`, and `0.5` sits inside it. -/
example : (![(0.5:ℝ)] : Vec ℝ 1) ∈ minkowskiDiff MDiff.I1.construct MDiff.I2.construct := by
  rw [Interval.minkDiff_exact MDiff.I1 MDiff.I2 MDiff.I2_nonempty]
  intro i
  fin_cases i
  constructor
  · show (MDiff.I1.minkDiff MDiff.I2).inf 0 ≤ (![(0.5:ℝ)] : Vec ℝ 1) 0
    norm_num [Interval.minkDiff, MDiff.I1, MDiff.I2]
  · show (![(0.5:ℝ)] : Vec ℝ 1) 0 ≤ (MDiff.I1.minkDiff MDiff.I2).sup 0
    norm_num [Interval.minkDiff, MDiff.I1, MDiff.I2]

/-- `0.9` sits outside it — cheap, since the representation itself already
excludes it. -/
example : (![(0.9:ℝ)] : Vec ℝ 1) ∉ minkowskiDiff MDiff.I1.construct MDiff.I2.construct := by
  rw [Interval.minkDiff_exact MDiff.I1 MDiff.I2 MDiff.I2_nonempty]
  intro h
  have h2 : (![(0.9:ℝ)] : Vec ℝ 1) 0 ≤ (MDiff.I1.minkDiff MDiff.I2).sup 0 := (h 0).2
  norm_num [Interval.minkDiff, MDiff.I1, MDiff.I2] at h2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
