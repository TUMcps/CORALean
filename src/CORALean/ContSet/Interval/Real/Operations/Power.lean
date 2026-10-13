import CORALean.ContSet.Interval.Real.Interval

/-!
# `Interval.power`

CORA's `base .^ k` for an interval base and a nonnegative integer exponent `k`
(`@interval/power.m`, integer branch): per coordinate the hull of `inf ^ k` and
`sup ^ k`, except that an even `k ≠ 0` over a box meeting `0` in its interior
has lower bound `0`.

Not covered: a negative integer exponent (CORA reduces it to `(1 ./ base) .^ -k`,
that is `Interval.recip` followed by this), a non-integer exponent (`NaN` below
`0`, no real counterpart) and an interval exponent.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Interval.power (I : Interval (Vec ℝ n)) (k : ℕ) : Interval (Vec ℝ n) where
  inf := fun i =>
    if k % 2 = 0 ∧ k ≠ 0 ∧ I.inf i < 0 ∧ 0 < I.sup i then 0
    else min (I.inf i ^ k) (I.sup i ^ k)
  sup := fun i => max (I.inf i ^ k) (I.sup i ^ k)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
