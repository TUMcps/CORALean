module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.ContSet.Interval.Real.Interval

@[expose] public section

/-!
# The result of `expmMixed` at a matrix zonotope

The matrix zonotope `eZ` and the interval matrices `eI` and `E` that CORA's `@matZonotope/expmMixed`
returns.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ========================================  MAIN TYPE  ========================================= --

/-- The outputs `eZ`, `eI` and `E` of `expmMixed` at a matrix zonotope, without the power arrays. -/
structure MatExp.ExpmMixedMatZono (n : ℕ) where
  /-- The Taylor terms up to the intermediate order, the exact terms of order zero to two first. -/
  eZ : Zonotope (Mat ℝ n n)
  /-- The terms past the intermediate order, up to the maximal order, and the remainder. -/
  eI : Interval (Mat ℝ n n)
  /-- The remainder after the maximal order. -/
  E : Interval (Mat ℝ n n)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
