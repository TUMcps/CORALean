module

public import CORALean.ContSet.Zonotope.Real.Operations.LinComb
public import CORALean.ContSet.Zonotope.Real.Operations.Plus
public import CORALean.Specification.STL.Definitions.DepReachState

@[expose] public section

/-!
# The time interval reachable set of the dependency preserving reachability algorithm

[1, Eq. 14-20] and line 9 of [1, Alg. 1]: `R(τ_i) = conv(H(t_i), H(t_{i+1})) ⊕ P(t_{i+1}) ⊕ C_i`,
the convex hull enclosed by Eq. (8), `Zonotope.linComb`, whose generators are `½(G₁+G₂)`,
`½(G₁-G₂)` and `½(c₁-c₂)`, `2γ_x + 1` of them, then those of `P_c(t_{i+1})`, of `D_{i+1}` and of
`C_i`. It takes the states at `t_i` and `t_{i+1}`.

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

/-- [1, Eq. 14-20]: `R(τ_i) = conv(H(t_i), H(t_{i+1})) ⊕ P(t_{i+1}) ⊕ C_i`. -/
noncomputable def STL.depReachInterval (s s' : STL.DepReachState n) : Zonotope (Vec ℝ n) :=
  ((s.H.linComb s'.H).plus (s'.Pc.plus s'.D)).plus s.C

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
