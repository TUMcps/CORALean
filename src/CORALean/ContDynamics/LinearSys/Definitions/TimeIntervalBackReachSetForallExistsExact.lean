module

public import CORALean.ContDynamics.LinearSys.Definitions.IsPerturbedTrajectory

@[expose] public section

/-!
# The states no admissible input can keep out of the target over an interval

[1, Def. 6]: the time-interval AE backward reachable set `R^{∀∃}(-τ)`,
as `backReachSetForallExistsExact` reads the time-point one, over the runs `U` and
`W` actually name — measurable and bounded, the class the solution exists in.

`∃t ∈ τ`, not `∀t ∈ τ`: the run has to pass through `Xend` at some time of the
interval, the same existential Prop. 2's proof relies on to put the union of
time-point sets inside this one. `U` and `W` are admissible over the whole of
`T`, since `u(·)` is chosen before `t` is.

## Inputs
* `sys` – linear system
* `T` – time domain
* `U` – admissible input set
* `W` – admissible disturbance set
* `Xend` – target set
* `τ` – target time interval

## Output
* states from which every input lets some disturbance hit the target in the interval

## References

* [1] [M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed Continuous-Time
      Linear Systems Using Set Propagation". IEEE Transactions on Automatic Control,
      2026.](../../../../../references/2026/wetzlinger-tac-backward-reachability.md)
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

/-- Every state that cannot avoid `Xend` over `τ`: for every admissible input
there is some admissible disturbance whose run passes through it. -/
def LinearSys.timeIntervalBackReachSetForallExistsExact (sys : LinearSys 𝕋 n) (T : Set ℝ)
    (U W Xend : S n) (τ : Set ℝ) : Set (Vec ℝ n) :=
  {x₀ | ∀ u : ℝ → Vec ℝ n, (∀ s ∈ T, u s ∈ construct U) →
      AEStronglyMeasurable u (volume.restrict T) →
      ∃ w x : ℝ → Vec ℝ n, sys.IsPerturbedTrajectory T U W x u w ∧
        x 0 = x₀ ∧ ∃ t ∈ τ, x t ∈ construct Xend}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
