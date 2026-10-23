module

public import CORALean.Specification.STLInterval.Operations.StlIntervalBounds
public import CORALean.Specification.STLInterval.Theorems.StlIntervalToRealInterval

@[expose] public section

/-!
# The constructor from stored bounds at a float scalar, read as reals

Over a float scalar `𝕋` `stlIntervalBounds` tests the lower bound against `0` and builds the
interval on the reals the bounds denote, so read as reals it is the interval of those reals.

## Inputs
* `lb` – lower bound
* `ub` – upper bound, or `inf`
* `lc` – whether the lower end is closed
* `rc` – whether the upper end is closed

## Hypotheses
* none

## Conclusion
* the float interval, read as reals, is the interval of the denoted bounds
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem STLInterval.stlIntervalBounds_toRealInterval (lb : 𝕋) (ub : WithTop 𝕋)
    (lc rc : Bool) : -- --- CONCL ---
    (STLInterval.stlIntervalBounds lb ub lc rc).toRealInterval =
      STLInterval.stlIntervalBounds (toReal lb) (ub.map toReal) lc rc := by -- --- PROOF ---
  -- the test of the lower bound is the one on the reals; then the constructor is
  unfold STLInterval.stlIntervalBounds
  by_cases h : toReal (0 : 𝕋) ≤ toReal lb
  · rw [dif_pos h, dif_pos (by simpa [toReal_zero_eq] using h),
      STLInterval.stlInterval_toRealInterval]
  · rw [dif_neg h, dif_neg (by simpa [toReal_zero_eq] using h)]
    rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
