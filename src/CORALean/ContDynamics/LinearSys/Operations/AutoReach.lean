module

public import CORALean.ContDynamics.LinearSys.Operations.AutoRun

@[expose] public section

/-!
# `Alg. 2` line 33: the reachable set

`autoReach`: `R̂([0,t_end])`, the union of the first `K` steps' time-interval sets that ran to
completion.

## Inputs
* `sys` – linear system
* `le` – comparison oracle on reals
* `X₀` – initial zonotope
* `U` – input zonotope
* `tend` – final time
* `εmax` – admissible error
* `ζ` – error budget share
* `ηmax` – maximal Taylor order
* `fuel` – number of shrinkings
* `K` – number of steps

## Output
* union of the time-interval sets of the completed steps

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control, 2023.
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

/-- [1, Alg. 2] line 33: `R̂([0,t_end])`, the union of the first `K` steps' time-interval
sets that ran to completion. -/
noncomputable def LinearSys.autoReach (sys : LinearSys 𝕋 n) (le : ℝ → ℝ → Bool)
    (X₀ U : Zonotope (Vec ℝ n)) (tend εmax ζ : ℝ) (ηmax fuel K : ℕ) : Set (Vec ℝ n) :=
  -- 33. R̂([0,t_end]), the union of the time-interval sets R̂(τ_k)
  ⋃ k < K, ⋃ s ∈ sys.autoRun le X₀ U tend εmax ζ ηmax fuel k,
    ⋃ r ∈ sys.autoStep le X₀ U tend εmax ζ ηmax fuel s, construct r.2

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
