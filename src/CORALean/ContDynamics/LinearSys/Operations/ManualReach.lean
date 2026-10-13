import CORALean.ContDynamics.LinearSys.Operations.ManualRun

/-!
# `Alg. 1` lines 12-13: the reachable set

`manualReach`: `R̂([0,t_end])`, the union of the first `K` steps' time-interval sets, `K`
standing for `t_end/Δt`.

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

/-- [1, Alg. 1] lines 12-13: `R̂([0,t_end])`, the union of the first `K` steps'
time-interval sets, `K` standing for `t_end/Δt`. -/
noncomputable def LinearSys.manualReach (sys : LinearSys 𝕋 n) (X₀ U : Zonotope (Vec ℝ n))
    (Δt : ℝ) (η ρ K : ℕ) : Set (Vec ℝ n) :=
  ⋃ k < K, construct (sys.manualStep X₀ U Δt η ρ (sys.manualRun X₀ U Δt η ρ k)).2

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
