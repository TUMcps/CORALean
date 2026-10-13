import CORALean.ContSet.Interval.Real.Interval
import CORALean.ContSet.Zonotope.Real.Zonotope
import CORALean.Global.Tensor

/-!
# The constants of line 1 of the dependency preserving reachability algorithm

[1, Alg. 1], line 1: `ũ = B c_u`, `U₀ = B(U ⊕ (-c_u))`, the propagation matrix `T` of Eq. (14),
the interval matrices `F` and `G` of Eq. (18) and the bloating `D` of Eq. (15), the values the
loop of Alg. 1 reuses at every step.

## References

* [1] N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, vol. 53, 2024, 101491.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real


-- ========================================  MAIN TYPE  ========================================= --

/-- `ũ`, `U₀`, `T`, `F`, `G` and `D` of [1, Alg. 1], line 1. -/
structure STL.DepReachConsts (n : ℕ) where
  ũ : Vec ℝ n
  U₀ : Zonotope (Vec ℝ n)
  T : Mat ℝ n n
  F : Interval (Mat ℝ n n)
  G : Interval (Mat ℝ n n)
  D : Zonotope (Vec ℝ n)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
