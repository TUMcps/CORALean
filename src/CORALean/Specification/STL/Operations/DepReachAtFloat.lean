module

public import CORALean.Specification.STL.Operations.DepReachAt
public import CORALean.Specification.STL.Operations.DepReachInitFloat
public import CORALean.Specification.STL.Operations.DepReachStepFloat

@[expose] public section

/-!
# The state of the dependency preserving reachability algorithm after `i` steps, over floats

[1, Alg. 1]: lines 2-3 in floats (`depReachInitFloat`) give the state at `t₀`, and each pass of
the loop, lines 5-7 in floats (`depReachStepFloat`), takes the state at `t_i` to that at
`t_{i+1}`. Soundness is `STL.depReachAtFloat_outer`.

## Inputs
* `A` – float dynamics matrix
* `Δt` – float time step
* `η` – Taylor order of the matrix exponential
* `cs` – float constants of the algorithm
* `X₀` – float initial set

## Output
* the float algorithm state after each number of steps
## References

* [1] N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, 2024.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The float state at `t_i = iΔt` of [1, Alg. 1]. -/
def STL.depReachAtFloat (A : Mat 𝕋 n n) (Δt : 𝕋) (η : ℕ) (cs : STL.DepReachConstsFloat 𝕋 n)
    (X₀ : Float.Zonotope (Vec 𝕋 n)) : ℕ → STL.DepReachStateFloat 𝕋 n
  -- 2. `t₀ ← 0`, `H(t₀) ← X₀`, `P_c(t₀), D₀ ← 0`, `C₀ ← interval(F X₀ ⊕ G ũ)`
  | 0 => STL.depReachInitFloat X₀ cs
  -- 5. the pass of the `for` loop from `t_i` to `t_{i+1}`
  | i + 1 => STL.depReachStepFloat A Δt η cs (STL.depReachAtFloat A Δt η cs X₀ i)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
