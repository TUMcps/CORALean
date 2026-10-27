module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# The disk example of Smith's convergence bound needs 18 iterations, not 17

`[1, Thm. 3]` bounds the distance to uniform after `m` iterations of the random-directions
algorithm by `(1 - γ / (n 2ⁿ⁻¹))^(m-1)`; for the disk in `ℝ²`, `γ = 1` and `n = 2`, this is
`(3/4)^(m-1)`. The numerical illustration (`[1, Sec. 4 (disk)]`) then says that "we will be within
1% of a uniform distribution after 17 iterations": `(3/4)^16 = 0.01002…` is above `1/100`, so the
bound certifies 1% from `m = 18`, where the exponent is `17`.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the disk bound is above one percent at 17 iterations and below it at 18

## References

* [1] [R. L. Smith. "Efficient Monte Carlo Procedures for Generating Points Uniformly Distributed
      Over Bounded Regions". Operations Research,
      1984.](../../../references/1984/smith-or-uniform-points.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

-- the exponent at `m = 17` is `16` and the bound is still above 1%; at `m = 18` it is below
theorem smith_disk_bound_iterations :
    (1 / 100 : ℝ) < (3 / 4) ^ (17 - 1) ∧ (3 / 4 : ℝ) ^ (18 - 1) < 1 / 100 := by
  norm_num

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
