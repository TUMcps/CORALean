import CORALean.ContSet.Interval.Real.Interval
import Mathlib.Order.Interval.Set.Defs

/-!
# `Interval.stlInterval`

CORA's `@interval/stlInterval`: the one-dimensional interval `[inf, sup]` as an STL time
interval, `stlInterval(I.inf, I.sup, true, true)`, closed at both ends (CORA throws unless the
interval is `1 × 1`; the type `Interval (Vec ℝ 1)` is that). The class `stlInterval` has no
counterpart in the tree, so the result is the set of times it denotes, a subset of `ℝ`. CORA's
constructor turns `lb > ub` into its empty interval, which `Set.Icc` is.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.stlInterval (I : Interval (Vec ℝ 1)) : Set ℝ :=
  let lb : ℝ := I.inf 0
  let ub : ℝ := I.sup 0
  Set.Icc lb ub


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
