module

public import CORALean.Global.Interfaces
public import CORALean.Specification.FiniteSignal.FiniteSignal
public import Mathlib.Order.Basic

@[expose] public section

/-!
# The value a list of breakpoints holds at a time

The breakpoints `(time,value)` of a finite signal, read as in `at.m`: the value of the first
breakpoint whose time exceeds `t`, the last value if there is none.

## Inputs
* `T` – time type
* `V` – value type

## Output
* the value the breakpoints hold at the time
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The value held at `t` by the breakpoints `L`. -/
def FiniteSignal.valueAt {T V : Type} [TimeOrder T] : List (T × V) → T → Option V
  | [], _ => none
  | [(_, v)], _ => some v
  | (b, v) :: x :: rest, t => if t < b then some v else FiniteSignal.valueAt (x :: rest) t

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
