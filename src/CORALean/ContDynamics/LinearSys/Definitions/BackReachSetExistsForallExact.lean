module

public import CORALean.ContDynamics.LinearSys.Definitions.IsPerturbedTrajectory

@[expose] public section

/-!
# The states one admissible input can steer into the target regardless

[1, Def. 7]: the time-point EA backward reachable set `R^{∃∀}(-t)`. A
state `x₀` is in it when some admissible input signal drives the perturbed
run into `Xend` at time `t` whatever admissible disturbance occurs. The `∀w`
guard ranges over the measurable admissible disturbances, the signals `Z_W(t)`
integrates and the ones a `IsPerturbedTrajectory` exists for.

`∃x` inside `∀w`, not `∀x`: quantifying the run itself universally would hold
vacuously for a `w` no run witnesses, and would silently enlarge the set.

## Inputs
* `sys` – linear system
* `T` – time domain
* `U` – admissible input set
* `W` – admissible disturbance set
* `Xend` – target set
* `t` – target time

## Output
* states from which some input reaches the target whatever the disturbance

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

/-- Every state from which some admissible input steers the perturbed run into
`Xend` at time `t`, whatever admissible disturbance occurs. -/
def LinearSys.backReachSetExistsForallExact (sys : LinearSys 𝕋 n) (T : Set ℝ)
    (U W Xend : S n) (t : ℝ) : Set (Vec ℝ n) :=
  {x₀ | ∃ u : ℝ → Vec ℝ n, (∀ s ∈ T, u s ∈ construct U) ∧
      AEStronglyMeasurable u (volume.restrict T) ∧
      ∀ w : ℝ → Vec ℝ n, (∀ s ∈ T, w s ∈ construct W) →
        AEStronglyMeasurable w (volume.restrict T) →
        ∃ x : ℝ → Vec ℝ n, sys.IsPerturbedTrajectory T U W x u w ∧
          x 0 = x₀ ∧ x t ∈ construct Xend}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
