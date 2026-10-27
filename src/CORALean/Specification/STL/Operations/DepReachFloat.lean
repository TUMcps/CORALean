module

public import CORALean.Specification.STL.Operations.DepReach
public import CORALean.Specification.STL.Operations.DepReachAtFloat
public import CORALean.Specification.STL.Operations.DepReachConstsOfFloat
public import CORALean.Specification.STL.Operations.DepReachIntervalFloat
public import CORALean.Specification.STL.Operations.DepReachPointFloat

@[expose] public section

/-!
# Dependency preserving reachability analysis, over floats

[1, Alg. 1] with every set held in `𝕋`: the constants of line 1 (`depReachConstsFloat`), the
state after `i` and `i + 1` steps (`depReachAtFloat`), and the point and interval sets of lines
8-9 (`depReachPointFloat`, `depReachIntervalFloat`). `STL.depReachFloat … i` is the `i`-th pair
`(R(t_i), R(τ_i))`. Soundness is `STL.depReachFloat_point_outer` and
`STL.depReachFloat_interval_outer`.

## Inputs
* `A` – float dynamics matrix
* `B` – float input matrix
* `X₀` – float initial set
* `U` – float input set
* `Δt` – float time step
* `κ` – Taylor order of the constants
* `η` – Taylor order of the matrix exponential
* `i` – step index

## Output
* the point and interval reachable sets of the step, in floats
## References

* [1] [N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, 2024.](../../../../../references/2024/kochdumper-nahs-stl-lti-verification.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 1] in `𝕋`: the `i`-th pair `(R(t_i), R(τ_i))` of the reach sequence. -/
def STL.depReachFloat (A : Mat 𝕋 n n) (B : Mat 𝕋 n m) (X₀ : Float.Zonotope (Vec 𝕋 n))
    (U : Float.Zonotope (Vec 𝕋 m)) (Δt : 𝕋) (κ η : ℕ) (i : ℕ) :
    Float.Zonotope (Vec 𝕋 n) × Float.Zonotope (Vec 𝕋 n) :=
  -- 1. `ũ, U₀, T, F, G, D`
  let cs := STL.depReachConstsFloat A B U Δt κ
  -- 2. `H(t_i), P_c(t_i), D_i, C_i`: lines 2-3, then `i` passes of the loop
  let s := STL.depReachAtFloat A Δt η cs X₀ i
  -- 5. … and one pass further, for `t_{i+1}`
  let s' := STL.depReachAtFloat A Δt η cs X₀ (i + 1)
  -- 8. `R(t_i) ← H(t_i) ⊕ P(t_i)`, with `P(t_i) = P_c(t_i) ⊕ D_i`
  let R_ti := STL.depReachPointFloat s
  -- 9. `R(τ_i) ← conv(H(t_i), H(t_{i+1})) ⊕ P(t_{i+1}) ⊕ C_i`
  let R_τi := STL.depReachIntervalFloat s s'
  (R_ti, R_τi)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
