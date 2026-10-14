module

public import CORALean.Specification.STLInterval.Operations.Basic
public import CORALean.Specification.STLInterval.Theorems.LowerStlInterval
public import Mathlib.Data.EReal.Operations

@[expose] public section

/-!
# The lower bound of `stlInterval(lb,ub,lc,rc)`

A nonempty interval built with a real lower bound `lb ≥ 0` has lower bound `lb`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- The interval `stlInterval(lb,ub,lc,rc)` has lower bound `≥ 0` if `lb` is. -/
theorem STLInterval.fields_stlIntervalBounds (lb : ℝ) (ub : WithTop ℝ) (lc rc : Bool) (h : 0 ≤ lb) :
    ∀ f, (STLInterval.stlIntervalBounds lb ub lc rc).fieldsOf = some f → 0 ≤ f.lower := by
  intro f hf
  rw [STLInterval.lower_stlInterval _ _ _ _ f hf]
  exact EReal.coe_nonneg.2 h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
