module

public import CORALean.ContSet.Interval.Real.Interval
public import Mathlib.Order.Interval.Set.Defs

@[expose] public section

/-!
# `Interval.stlInterval`

CORA's `@interval/stlInterval`: the one-dimensional interval `[inf, sup]` as an STL time
interval, `stlInterval(I.inf, I.sup, true, true)`, closed at both ends (CORA throws unless the
interval is `1 × 1`; the type `Interval (Vec ℝ 1)` is that). The class `stlInterval` has no
counterpart in the tree, so the result is the set of times it denotes, a subset of `ℝ`. CORA's
constructor turns `lb > ub` into its empty interval, which `Set.Icc` is.

## Inputs
* `I` – interval box

## Output
* closed real interval between the first entries of the bounds
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.stlInterval (I : Interval (Vec ℝ 1)) : Set ℝ :=
  let lb : ℝ := I.inf 0
  let ub : ℝ := I.sup 0
  Set.Icc lb ub


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
