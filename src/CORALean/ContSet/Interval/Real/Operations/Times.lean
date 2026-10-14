module

public import CORALean.ContSet.Interval.Real.Operations.Basic

@[expose] public section

/-!
# `Interval.times`

CORA's `@interval/times` at two intervals: the entrywise product, each coordinate the hull of the
four corner products (`mulLo`, `mulHi`). CORA's `NaN` convention for `0 * ∞` has no counterpart in
`ℝ`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.times (I J : Interval (Vec ℝ n)) : Interval (Vec ℝ n) where
  inf := fun i => Interval.mulLo (I.inf i) (I.sup i) (J.inf i) (J.sup i)
  sup := fun i => Interval.mulHi (I.inf i) (I.sup i) (J.inf i) (J.sup i)


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
