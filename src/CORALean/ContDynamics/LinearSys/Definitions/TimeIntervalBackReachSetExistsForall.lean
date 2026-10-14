module

public import CORALean.ContDynamics.LinearSys.Definitions.PerturbedTrajectory

@[expose] public section

/-!
# The states one admissible input can steer into the target over an interval

[1, Def. 7]: the time-interval EA backward reachable set `R^{∃∀}(-τ)`,
as `backReachSetExistsForall` reads the time-point one and
`timeIntervalBackReachSetForallExists` reads Def. 6's: the guards range over
the measurable admissible signals.

`∃t ∈ τ`, not `∀t ∈ τ`: the run has to pass through `Xend` at some time of the
interval. `u(·)` is chosen before both `w(·)` and `t`, so it is admissible over
the whole of `T`.

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed
      Continuous-Time Linear Systems Using Set Propagation". IEEE Transactions on
      Automatic Control, 71(1):352-367, 2026.
-/

-- Authors:       Claude Sonnet 5
-- Written:       19-September-2026
-- Last update:   10-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar MeasureTheory

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every state from which some admissible input steers the perturbed run
through `Xend` at some time in `τ`, whatever admissible disturbance occurs. -/
def LinearSys.timeIntervalBackReachSetExistsForall (sys : LinearSys 𝕋 n) (T : Set ℝ)
    (U W Xend : S n) (τ : Set ℝ) : Set (Vec ℝ n) :=
  {x₀ | ∃ u : ℝ → Vec ℝ n, (∀ s ∈ T, u s ∈ construct U) ∧
      AEStronglyMeasurable u (volume.restrict T) ∧
      ∀ w : ℝ → Vec ℝ n, (∀ s ∈ T, w s ∈ construct W) →
        AEStronglyMeasurable w (volume.restrict T) →
        ∃ x : ℝ → Vec ℝ n, sys.PerturbedTrajectory T U W x u w ∧
          x 0 = x₀ ∧ ∃ t ∈ τ, x t ∈ construct Xend}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
