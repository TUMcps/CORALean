module

public import CORALean.Specification.STL.Operations.DepReachAt
public import CORALean.Specification.STL.Operations.DepReachConstsOf
public import CORALean.Specification.STL.Operations.DepReachInterval
public import CORALean.Specification.STL.Operations.DepReachPoint

@[expose] public section

/-!
# Dependency preserving reachability analysis

[1, Alg. 1]: the reach sequence `R(t₀), R(τ₀), R(t₁), R(τ₁), ...` of Eq. (11) for
`ẋ = Ax + Bu`, `X₀ = ⟨c_x, G_x⟩_Z`, `U = ⟨c_u, G_u⟩_Z`, the time step `Δt` and the truncation order
`κ`; `STL.depReach … i` is its `i`-th pair `(R(t_i), R(τ_i))`. The final time only bounds `i`.

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

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 1]: the `i`-th pair `(R(t_i), R(τ_i))` of the reach sequence. -/
noncomputable def STL.depReach (A : Mat ℝ n n) (B : Mat ℝ n m) (X₀ : Zonotope (Vec ℝ n))
    (U : Zonotope (Vec ℝ m)) (Δt : ℝ) (κ : ℕ) (i : ℕ) :
    Zonotope (Vec ℝ n) × Zonotope (Vec ℝ n) :=
  let cs := STL.depReachConsts A B U Δt κ                          -- line 1
  let s := STL.depReachAt A Δt cs X₀ i                              -- lines 2-3, 5-7: state at t_i
  let s' := STL.depReachAt A Δt cs X₀ (i + 1)                       -- state at t_{i+1}
  (STL.depReachPoint s, STL.depReachInterval s s')                  -- lines 8-9

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
