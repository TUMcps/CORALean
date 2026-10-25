module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.Global.Tensor

@[expose] public section

/-!
# The state of the loop of the dependency preserving reachability algorithm

[1, Alg. 1]: what the loop carries from `t_i` to `t_{i+1}`: the homogeneous solution `H(t_i)`,
the particular solution `P_c(t_i)` of the constant inputs, the interval enclosure `D_i` of the
bloating and the curvature set `C_i`. `P(t_i) = P_c(t_i) ⊕ D_i` is not stored.

## References

* [1] N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real


-- ========================================  MAIN TYPE  ========================================= --

/-- `H(t_i)`, `P_c(t_i)`, `D_i` and `C_i` of [1, Alg. 1]. -/
structure STL.DepReachState (n : ℕ) where
  H : Zonotope (Vec ℝ n)
  Pc : Zonotope (Vec ℝ n)
  D : Zonotope (Vec ℝ n)
  C : Zonotope (Vec ℝ n)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
