module

public import CORALean.Specification.FiniteSignal.FiniteSignal
public import CORALean.Specification.FiniteSignal.Operations.CombineEmit
public import Mathlib.Order.Basic

@[expose] public section

/-!
# The loop of `combine`

The `while` loop of `combine.m` on the breakpoints of the two signals, until one signal is used
up. The two `if`s of the loop body, advancing the left signal if `ltime <= rtime` and the right
one if `ltime >= rtime`, are the three cases `ltime < rtime`, `ltime = rtime` and `ltime > rtime`.

## Inputs
* `T` – time type
* `V` – value type of the inputs
* `W` – value type of the result
* `op` – binary operator on values

## Output
* the combined breakpoints of the two lists
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The breakpoints `(tim(k),val(k))` the loop produces from the breakpoints `lhs` and `rhs`. -/
def FiniteSignal.combineLoop {T V W : Type} [LinearOrder T] [DecidableEq W] (op : V → V → W) :
    List (T × V) → List (T × V) → List (T × W)
  | l :: ls, r :: rs =>
    -- ltime < rtime: progress in left signal
    if l.1 < r.1 then FiniteSignal.combineEmit op l.1 (op l.2 r.2) ls (r :: rs)
      (FiniteSignal.combineLoop op ls (r :: rs))
    -- ltime = rtime: progress in both signals
    else if l.1 = r.1 then FiniteSignal.combineEmit op l.1 (op l.2 r.2) ls rs
      (FiniteSignal.combineLoop op ls rs)
    -- ltime > rtime: progress in right signal
    else FiniteSignal.combineEmit op r.1 (op l.2 r.2) (l :: ls) rs
      (FiniteSignal.combineLoop op (l :: ls) rs)
  | _, _ => []
termination_by lhs rhs => lhs.length + rhs.length

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
