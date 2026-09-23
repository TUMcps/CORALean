import CORALean.ContDynamics.LinearSys.Definitions.PerturbedIntegralTrajectory

/-!
# The time-interval minimal backward reachable set, with Carathéodory runs

[1, Def. 6]'s time-interval set `R^{∀∃}(-τ)` over `PerturbedIntegralTrajectory`
instead of `PerturbedTrajectory`, as `integralBackReachSetForallExists` reads
the time-point one. The reading is not cosmetic here: a pointwise derivative is
measurable, so under `PerturbedTrajectory` a non-measurable admissible `u(·)`
admits no run at all, the `∃w` under it fails, and `R^{∀∃}(-τ)` is empty as
soon as `U` holds two points. [1, Thm. 1] would then be `∅ ⊆ …`, true and
empty. Over the runs `U` and `W` actually name — measurable and bounded, the
class the solution exists in — it says something.

`∃t ∈ τ`, not `∀t ∈ τ`: the run has to pass through `Xend` at some time of the
interval, matching `timeIntervalBackReachSetForallExists`.

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

/-- Every state that cannot avoid `Xend` over `τ`: for every admissible input
there is some admissible disturbance whose run passes through it. -/
def LinearSys.integralTimeIntervalBackReachSetForallExists (sys : LinearSys 𝕋 n) (T : Set ℝ)
    (U W Xend : S n) (τ : Set ℝ) : Set (Vec ℝ n) :=
  {x₀ | ∀ u : ℝ → Vec ℝ n, (∀ s ∈ T, u s ∈ construct U) →
      AEStronglyMeasurable u (volume.restrict T) →
      ∃ w x : ℝ → Vec ℝ n, sys.PerturbedIntegralTrajectory T U W x u w ∧
        x 0 = x₀ ∧ ∃ t ∈ τ, x t ∈ construct Xend}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
