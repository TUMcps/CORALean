import CORALean.ContDynamics.LinearSys.Operations.AutoRun

/-!
# `Alg. 2` line 33: the reachable set

`autoReach`: `R̂([0,t_end])`, the union of the first `K` steps' time-interval sets that ran to
completion.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Claude Sonnet 5
-- Written:       19-September-2026
-- Last update:   ---
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
  ⋃ k < K, ⋃ s ∈ sys.autoRun le X₀ U tend εmax ζ ηmax fuel k,
    ⋃ r ∈ sys.autoStep le X₀ U tend εmax ζ ηmax fuel s, construct r.2

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
