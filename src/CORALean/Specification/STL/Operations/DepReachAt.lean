module

public import CORALean.Specification.STL.Operations.DepReachInit
public import CORALean.Specification.STL.Operations.DepReachStep

@[expose] public section

/-!
# The state of the dependency preserving reachability algorithm after `i` steps

[1, Alg. 1]: lines 2-3 give the state at `t₀`, and each pass of the loop, lines 5-7, takes the
state at `t_i` to that at `t_{i+1}`; this is the state after `i` passes.

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

/-- The state at `t_i = iΔt` of [1, Alg. 1]. -/
noncomputable def STL.depReachAt (A : Mat ℝ n n) (Δt : ℝ) (cs : STL.DepReachConsts n)
    (X₀ : Zonotope (Vec ℝ n)) : ℕ → STL.DepReachState n
  -- 2. `t₀ ← 0`, `H(t₀) ← X₀`, `P_c(t₀), D₀ ← 0`, `C₀ ← interval(F X₀ ⊕ G ũ)`
  | 0 => STL.depReachInit X₀ cs
  -- 5. the pass of the `for` loop from `t_i` to `t_{i+1}`
  | i + 1 => STL.depReachStep A Δt cs (STL.depReachAt A Δt cs X₀ i)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
