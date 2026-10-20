module

public import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalStep
public import CORALean.ContDynamics.NonlinearSys.Operations.RelinReach

@[expose] public section

/-!
# Step `i` of the re-linearization loop, over its whole interval

`relinReach` reaches the state at `iΔt` only; this is the set it is in at every
time of step `i`: `LinearSys.timeIntervalStep` of the linearized system at
`(steps i).A`, applied to what `relinReach` reaches at the step's start, plus
step `i`'s own input enclosure — the shape `IsTrajectory.timeInterval_outer`
proves, not one invented ahead of it.

`R(τ_s)` of [1, Alg. 1], its line 13, and what its line 22 collects into the
union the algorithm returns.

## Inputs
* `sys` – system
* `U` – input set
* `o` – maximum order
* `Δt` – step size
* `η` – Taylor terms
* `steps` – linearization steps
* `Ud` – input enclosures per step
* `R₀` – initial set
* `i` – step index

## Hypotheses
* `ho` – order positive

## Output
* the enclosure of step `i` over its interval

## References

* [1] N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set
      Representation for Reachability Analysis". IEEE Transactions on Automatic
      Control, 2021.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The enclosure of step `i` of the re-linearization loop over its whole
interval, from what `relinReach` reaches at `iΔt` and step `i`'s input
enclosure. -/
noncomputable def NonlinearSys.relinTimeInterval (sys : NonlinearSys n m) {U : S m} (o : ℕ)
    (ho : 0 < o) (Δt : ℝ) (η : ℕ) (steps : ℕ → sys.LinStep U) (Ud : ℕ → S n) (R₀ : S n) (i : ℕ) :
    S n :=
  ((NonlinearSys.linearize (steps i).A).timeIntervalStep Δt η
    (sys.relinReach ⟨R₀, 0, i⟩ ⟨Δt, o, ho⟩ steps Ud)) ⊞ Ud i

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
