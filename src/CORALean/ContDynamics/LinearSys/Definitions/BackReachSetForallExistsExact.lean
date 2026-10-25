module

public import CORALean.ContDynamics.LinearSys.Definitions.IsPerturbedTrajectory

@[expose] public section

/-!
# The states no admissible input can keep out of the target

[1, Def. 6]: the time-point AE backward reachable set `R^{∀∃}(-t)`. A
state `x₀` is in it when, whatever admissible input signal is applied, some
admissible disturbance signal still drives the perturbed run into `Xend` at
time `t`. The paper's `U` and `W` are the signals for which the solution
`ξ(t;x₀,u(·),w(·))` exists at all, for a linear system the measurable bounded
ones, so the `∀u` guard carries measurability as well as admissibility: it
quantifies over the same signals `Z_U(t)` integrates, no more and no fewer.

## Inputs
* `sys` – linear system
* `T` – time domain
* `U` – admissible input set
* `W` – admissible disturbance set
* `Xend` – target set
* `t` – target time

## Output
* states from which every input lets some disturbance reach the target

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed Continuous-Time
      Linear Systems Using Set Propagation". IEEE Transactions on Automatic Control, 2026.
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

/-- Every state that cannot avoid `Xend` at time `t`: for every admissible
input there is some admissible disturbance whose run lands there. -/
def LinearSys.backReachSetForallExistsExact (sys : LinearSys 𝕋 n) (T : Set ℝ)
    (U W Xend : S n) (t : ℝ) : Set (Vec ℝ n) :=
  {x₀ | ∀ u : ℝ → Vec ℝ n, (∀ s ∈ T, u s ∈ construct U) →
      AEStronglyMeasurable u (volume.restrict T) →
      ∃ w x : ℝ → Vec ℝ n, sys.IsPerturbedTrajectory T U W x u w ∧
        x 0 = x₀ ∧ x t ∈ construct Xend}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
