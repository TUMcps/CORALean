import CORALean.Specification.STL.Operations.DepReachAt

/-!
# The homogeneous solution has the generators of `X₀`

[1, Alg. 1]: `H(t_{i+1}) = e^{AΔt}H(t_i) ⊕ T ũ` maps the generators and appends none, so
`H(t_i)` has the `γ_x` generators of `X₀` at every `i`: the first `γ_x` indices of `H_i` in
[1, Prop. 1].

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


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.depReachAt_H_h (A : Mat ℝ n n) (Δt : ℝ) (cs : STL.DepReachConsts n)
    (X₀ : Zonotope (Vec ℝ n)) (i : ℕ) : (STL.depReachAt A Δt cs X₀ i).H.h = X₀.h := by
  induction i with
  | zero => rfl
  | succ i ih => exact ih

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
