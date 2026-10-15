module

public import CORALean.ContSet.Interval.Real.Interval

@[expose] public section

/-!
# `MatExp.ExpmMixed`: the outputs of `expmMixed`

CORA's `[eI, eI2, iPow, iPow2, E] = expmMixed(intMat, r, intermediateOrder, maxOrder)`: the first
part of the evaluation, the second part, and the remainder. The two cell arrays of powers are
intermediate values of the evaluation and are not part of the result here.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ========================================  MAIN TYPE  ========================================= --

/-- The interval matrices `eI`, `eI2` and `E` that `expmMixed` returns. -/
structure MatExp.ExpmMixed (n : ℕ) where
  /-- The Taylor terms up to the intermediate order, the exact terms of order zero to two first. -/
  eI : Interval (Mat ℝ n n)
  /-- The terms past the intermediate order, up to the maximal order, and the remainder. -/
  eI2 : Interval (Mat ℝ n n)
  /-- The remainder after the maximal order. -/
  E : Interval (Mat ℝ n n)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
