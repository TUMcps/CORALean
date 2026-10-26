module

public import CORALean.Global.Float.Instances.Real.Instances
public import CORALean.Global.Float.TimeOrder
public import CORALean.Specification.PointSegmentSignal.Operations.AllTrue
public import CORALean.Specification.PointSegmentSignal.Theorems.RelevantStartMapTime
public import CORALean.Specification.PointSegmentSignal.Theorems.RelevantStopMapTime

@[expose] public section

/-!
# Whether a value holds everywhere at a float time type, read as reals

Over a float scalar `𝕋` `allTrue` finds the values within the bounds by exact comparisons of the
time points with them (`TimeOrder`), so the signal read as reals, between the bounds read as reals,
gives the float answer.

## Inputs
* `s` – signal
* `lb` – lower bound
* `ub` – upper bound, or `inf`
* `lc` – whether the lower end is closed
* `rc` – whether the upper end is closed
* `cond` – condition on values

## Hypotheses
* none

## Conclusion
* the answer on the signal and bounds read as reals is the float one
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PointSegmentSignal.allTrue_mapTime (s : PointSegmentSignal 𝕋) (lb : 𝕋)
    (ub : WithTop 𝕋) (lc rc : Bool) (cond : Bool → Bool) :
    (s.mapTime toReal).allTrue (toReal lb) (ub.map toReal) lc rc cond =
      s.allTrue lb ub lc rc cond := by
  -- the same values between the same indices
  unfold PointSegmentSignal.allTrue
  rw [PointSegmentSignal.relevantStart_mapTime, PointSegmentSignal.relevantStop_mapTime]
  rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
