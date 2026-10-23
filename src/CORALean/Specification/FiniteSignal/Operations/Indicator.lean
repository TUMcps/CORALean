module

public import CORALean.Specification.FiniteSignal.FiniteSignal
public import CORALean.Specification.FiniteSignal.Operations.Mk

@[expose] public section

/-!
# The indicator signal of an interval

`sig = indicator(dur,int,val)` of `indicator.m`: the signal of duration `dur` that is `val` on the
interval `int` and false elsewhere, in one of five cases by how `int` lies in `[0,dur]`. `int` is
given by its bounds `lo` and `hi`, time stamps like `dur`; an unbounded end behaves as a bound
outside `[0,dur]`. CORA throws for an empty or singleton interval and, in the constructor, for a
negative `dur`; both are `none`. Generic over the time type: at a float scalar the comparisons are
exact (`TimeOrder`), so nothing rounds.

## Inputs
* `T` – time type
* `dur` – signal duration
* `lo` – interval lower bound
* `hi` – interval upper bound
* `val` – value on the interval

## Output
* the signal that is `val` on the interval, or none if the interval is degenerate
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `sig = indicator(dur,int,val)`. -/
def FiniteSignal.indicator? {T : Type} [TimeOrder T] [Zero T] (dur lo hi : T) (val : Bool) :
    Option (FiniteSignal T Bool) :=
  -- interval must not be degenerate
  if hi ≤ lo then none
  -- default value or interval out of range
  else if val = false ∨ hi ≤ 0 ∨ dur ≤ lo then FiniteSignal.mk? [dur] [false]
  -- interval completely covers range
  else if lo ≤ 0 ∧ dur ≤ hi then FiniteSignal.mk? [dur] [val]
  -- interval overlaps left range bound
  else if lo ≤ 0 then FiniteSignal.mk? [hi, dur] [val, false]
  -- interval overlaps right range bound
  else if dur ≤ hi then FiniteSignal.mk? [lo, dur] [false, val]
  -- interval is contained in range
  else FiniteSignal.mk? [lo, hi, dur] [false, val, false]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
