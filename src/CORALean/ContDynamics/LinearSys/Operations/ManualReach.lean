module

public import CORALean.ContDynamics.LinearSys.Operations.ManualRun

@[expose] public section

/-!
# `Alg. 1` lines 12-13: the reachable set

`manualReach`: `R̂([0,t_end])`, the union of the first `K` steps' time-interval sets, `K`
standing for `t_end/Δt`.

## Inputs
* `sys` – linear system
* `X₀` – initial zonotope
* `U` – input zonotope
* `Δt` – step length
* `η` – Taylor order
* `ρ` – zonotope order
* `K` – number of steps

## Output
* union of the time-interval sets of the steps

## References

* [1] [M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control,
      2023.](../../../../../references/2023/wetzlinger-fully-automated-verification.md)
-/

-- Authors:       Claude Sonnet 5
-- Written:       19-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 1] lines 12-13: `R̂([0,t_end])`, the union of the first `K` steps'
time-interval sets, `K` standing for `t_end/Δt`. -/
noncomputable def LinearSys.manualReach (sys : LinearSys 𝕋 n) (X₀ U : Zonotope (Vec ℝ n))
    (Δt : ℝ) (η ρ K : ℕ) : Set (Vec ℝ n) :=
  -- 12.-13. R̂([0,t_end]), the union of the time-interval sets R̂(τ_k)
  ⋃ k < K, construct (sys.manualStep X₀ U Δt η ρ (sys.manualRun X₀ U Δt η ρ k)).2

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
