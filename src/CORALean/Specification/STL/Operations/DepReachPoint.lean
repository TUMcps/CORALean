module

public import CORALean.ContSet.Zonotope.Real.Operations.Plus
public import CORALean.Specification.STL.Definitions.DepReachState

@[expose] public section

/-!
# The time point reachable set of the dependency preserving reachability algorithm

[1, Eq. 14-20] and line 8 of [1, Alg. 1]: `R(t_i) = H(t_i) ⊕ P(t_i)`, `P(t_i) = P_c(t_i) ⊕ D_i`: the
generators of `H(t_i)`, then those of `P_c(t_i)`, then those of `D_i`.

Refinement pending: CORA computes this in doubles, and its refinement generic over `𝕋` (a zonotope
computation over `𝕋` with directed rounding) is not yet written.

## References

* [1] N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, vol. 53, 2024, 101491.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Eq. 14-20]: `R(t_i) = H(t_i) ⊕ P(t_i)`. -/
def STL.depReachPoint (s : STL.DepReachState n) : Zonotope (Vec ℝ n) :=
  s.H.plus (s.Pc.plus s.D)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
