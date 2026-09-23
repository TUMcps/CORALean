import CORALean.ContDynamics.LinearSys.Definitions.PerturbedIntegralTrajectory

/-!
# The time-interval maximal backward reachable set, with Carathéodory runs

[1, Def. 7]'s time-interval set `R^{∃∀}(-τ)` over `PerturbedIntegralTrajectory`
instead of `PerturbedTrajectory`, as `integralBackReachSetExistsForall` reads
the time-point one and `integralTimeIntervalBackReachSetForallExists` reads
Def. 6's. The reading decides whether the set says anything: a pointwise
derivative is measurable, so under `PerturbedTrajectory` a non-measurable
admissible `w(·)` admits no run at all, the `∀w` guard then quantifies over
disturbances nothing realizes, and the set is empty as soon as `W` holds two
points — which would make [1, Thm. 2] an inner approximation of `∅`.

`∃t ∈ τ`, not `∀t ∈ τ`: the run has to pass through `Xend` at some time of the
interval, matching `timeIntervalBackReachSetExistsForall`. `u(·)` is chosen
before both `w(·)` and `t`, so it is admissible over the whole of `T`.

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of
      Perturbed Continuous-Time Linear Systems Using Set Propagation". arXiv:2310.19083,
      2023.
-/

-- Authors:       Tobias Ladner
-- Written:       19-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar MeasureTheory

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every state from which some admissible input steers the perturbed run
through `Xend` at some time in `τ`, whatever admissible disturbance occurs. -/
def LinearSys.integralTimeIntervalBackReachSetExistsForall (sys : LinearSys 𝕋 n) (T : Set ℝ)
    (U W Xend : S n) (τ : Set ℝ) : Set (Vec ℝ n) :=
  {x₀ | ∃ u : ℝ → Vec ℝ n, (∀ s ∈ T, u s ∈ construct U) ∧
      AEStronglyMeasurable u (volume.restrict T) ∧
      ∀ w : ℝ → Vec ℝ n, (∀ s ∈ T, w s ∈ construct W) →
        AEStronglyMeasurable w (volume.restrict T) →
        ∃ x : ℝ → Vec ℝ n, sys.PerturbedIntegralTrajectory T U W x u w ∧
          x 0 = x₀ ∧ ∃ t ∈ τ, x t ∈ construct Xend}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
