module

public import CORALean.Specification.STLInterval.Definitions.MemBounds
public import CORALean.Specification.STLInterval.Operations.Basic
public import CORALean.Specification.STLInterval.Theorems.SetStlInterval
public import Mathlib.Data.EReal.Operations

@[expose] public section

/-!
# `stlInterval(lb,ub,lc,rc)` with real bounds denotes the times between them

The interval with a real lower bound and an upper bound that is real or `inf`, each end closed as
its flag says, contains `t` exactly when `STLInterval.memBounds` holds.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- The times of `stlInterval(lb,ub,lc,rc)` are those between the bounds. -/
theorem STLInterval.mem_set_stlIntervalBounds (lb : ℝ) (ub : WithTop ℝ) (lc rc : Bool) (t : ℝ) :
    t ∈ (STLInterval.stlIntervalBounds lb ub lc rc).set ↔ STLInterval.memBounds lb ub lc rc t := by
  rw [STLInterval.stlIntervalBounds, STLInterval.set_stlInterval]
  induction ub using WithTop.recTopCoe with
  | top => simp [STLInterval.rawSet, STLInterval.memBounds, eq_comm]
  | coe u => simp [STLInterval.rawSet, STLInterval.memBounds, eq_comm]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
