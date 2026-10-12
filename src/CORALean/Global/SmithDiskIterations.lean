import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The disk example of Smith's convergence bound needs 18 iterations, not 17

`[1, Thm. 3]` bounds the distance to uniform after `m` iterations of the random-directions
algorithm by `(1 - γ / (n 2ⁿ⁻¹))^(m-1)`; for the disk in `ℝ²`, `γ = 1` and `n = 2`, this is
`(3/4)^(m-1)`. The numerical illustration (`[1, Sec. 4 (disk)]`) then says that "we will be within
1% of a uniform distribution after 17 iterations": `(3/4)^16 = 0.01002…` is above `1/100`, so the
bound certifies 1% from `m = 18`, where the exponent is `17`.

## References

* [1] R. L. Smith. "Efficient Monte Carlo Procedures for Generating Points Uniformly Distributed
      Over Bounded Regions". Operations Research 32(6), pp. 1296-1308, 1984.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

-- the exponent at `m = 17` is `16` and the bound is still above 1%; at `m = 18` it is below
theorem smith_disk_bound_iterations :
    (1 / 100 : ℝ) < (3 / 4) ^ (17 - 1) ∧ (3 / 4 : ℝ) ^ (18 - 1) < 1 / 100 := by
  norm_num

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
