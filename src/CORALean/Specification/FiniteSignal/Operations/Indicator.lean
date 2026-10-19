module

public import CORALean.Specification.FiniteSignal.FiniteSignal
public import CORALean.Specification.FiniteSignal.Operations.Mk
public import Mathlib.Data.EReal.Operations

@[expose] public section

/-!
# The indicator signal of an interval

`sig = indicator(dur,int,val)` of `indicator.m`: the signal of duration `dur` that is `val` on the
interval `int` and false elsewhere, as one of five cases by how the interval lies in `[0,dur]`.
The `interval` `int` is given by its bounds `lo` and `hi`, extended reals as `interval(lb,ub)`
allows `inf`. CORA throws for an empty or singleton interval (`volume(int) == 0`) and in the
constructor for a negative `dur`; both are `none`. `val` is a logical value (CORA's default
`true`).

Refinement pending: CORA computes this in doubles, and its refinement generic over `𝕋` (time
stamps over `𝕋`, rounded outward) is not yet written.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `sig = indicator(dur,int,val)`. -/
noncomputable def FiniteSignal.indicator? (dur : ℝ) (lo hi : EReal) (val : Bool) :
    Option (FiniteSignal ℝ Bool) :=
  -- interval must not be degenerate
  if hi ≤ lo then none
  -- default value or interval out of range
  else if val = false ∨ hi ≤ 0 ∨ (dur : EReal) ≤ lo then FiniteSignal.mk? [dur] [false]
  -- interval completely covers range
  else if lo ≤ 0 ∧ (dur : EReal) ≤ hi then FiniteSignal.mk? [dur] [val]
  -- interval overlaps left range bound
  else if lo ≤ 0 then FiniteSignal.mk? [hi.toReal, dur] [val, false]
  -- interval overlaps right range bound
  else if (dur : EReal) ≤ hi then FiniteSignal.mk? [lo.toReal, dur] [false, val]
  -- interval is contained in range
  else FiniteSignal.mk? [lo.toReal, hi.toReal, dur] [false, val, false]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
