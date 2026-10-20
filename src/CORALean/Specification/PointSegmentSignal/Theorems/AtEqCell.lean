module

public import CORALean.Specification.PointSegmentSignal.Operations.At
public import CORALean.Specification.PointSegmentSignal.Operations.Cell
public import Mathlib.Order.Basic

@[expose] public section

/-!
# The value a signal reads is the stored value at its index

`at` reads the stored value at the index `cell`.

## Inputs
* `T` – time type
* `s` – signal
* `t` – time

## Hypotheses
* none

## Conclusion
* the value is the stored value at the cell index
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- The value `at` reads is the stored value at index `cell`. -/
theorem PointSegmentSignal.at_eq_cell {T : Type} [LinearOrder T] (s : PointSegmentSignal T)
    (t : T) :
    s.at t = s.values.getD (s.cell t) false := by
  unfold PointSegmentSignal.at PointSegmentSignal.cell
  dsimp only
  split_ifs <;> rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
