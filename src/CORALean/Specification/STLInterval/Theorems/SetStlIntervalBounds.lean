module

public import CORALean.Specification.STLInterval.Theorems.Basic
public import CORALean.Specification.STLInterval.Definitions.IsInBounds
public import CORALean.Specification.STLInterval.Operations.Basic
public import CORALean.Specification.STLInterval.Operations.StlIntervalBounds
public import CORALean.Specification.STLInterval.Theorems.SetStlInterval
public import Mathlib.Data.EReal.Operations

@[expose] public section

/-!
# `stlInterval(lb,ub,lc,rc)` with real bounds denotes the times between them

The interval with a real lower bound and an upper bound that is real or `inf`, each end closed as
its flag says, contains `t` exactly when `STLInterval.IsInBounds` holds.

## Inputs
* `lb` – lower bound
* `ub` – upper bound
* `lc` – lower bound is closed
* `rc` – upper bound is closed
* `t` – time

## Hypotheses
* `hlb` – the lower bound is nonnegative

## Conclusion
* the time is in the interval iff it lies between the bounds
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- The times of `stlInterval(lb,ub,lc,rc)` are those between the bounds. -/
theorem STLInterval.mem_set_stlIntervalBounds (lb : ℝ) (ub : WithTop ℝ) (lc rc : Bool)
    (hlb : 0 ≤ lb) (t : ℝ) :
    t ∈ (STLInterval.stlIntervalBounds lb ub lc rc).set ↔
      STLInterval.IsInBounds lb ub lc rc t := by
  rw [STLInterval.stlIntervalBounds, dif_pos (by simpa using hlb), STLInterval.set_stlInterval]
  induction ub using WithTop.recTopCoe with
  | top => simp [STLInterval.rawSet, STLInterval.IsInBounds, eq_comm]
  | coe u => simp [STLInterval.rawSet, STLInterval.IsInBounds, eq_comm]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
