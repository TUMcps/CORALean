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

Refinement pending: CORA computes this in doubles, and its refinement generic over `𝕋` (a zonotope
computation over `𝕋` with directed rounding) is not yet written.

## Inputs
* `A` – dynamics matrix
* `B` – input matrix
* `X₀` – initial set
* `U` – input set
* `Δt` – time step
* `κ` – Taylor order
* `i` – step index

## Output
* the point and interval reachable sets of the step

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
  -- 1. `ũ, U₀, T, F, G, D`
  let cs := STL.depReachConsts A B U Δt κ
  -- 2. `H(t_i), P_c(t_i), D_i, C_i`: lines 2-3, then `i` passes of the loop
  let s := STL.depReachAt A Δt cs X₀ i
  -- 5. … and one pass further, for `t_{i+1}`
  let s' := STL.depReachAt A Δt cs X₀ (i + 1)
  -- 8. `R(t_i) ← H(t_i) ⊕ P(t_i)`, with `P(t_i) = P_c(t_i) ⊕ D_i`
  let R_ti := STL.depReachPoint s
  -- 9. `R(τ_i) ← conv(H(t_i), H(t_{i+1})) ⊕ P(t_{i+1}) ⊕ C_i`
  let R_τi := STL.depReachInterval s s'
  (R_ti, R_τi)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
