import CORALean.ContDynamics.LinearSys.Operations.Discretize
import CORALean.ContDynamics.LinearSysDT.Operations
import CORALean.ContDynamics.NonlinearSys.LinStep
import CORALean.ContDynamics.NonlinearSys.Operations.Linearize

/-!
# The re-linearization loop

CORA's `nonlinearSys/reach`: one linearization per time step, the enclosure
reached at the end of a step becoming the initial set of the next. Step `i` runs
the linear machinery of step `i`'s own system for exactly one step, so the whole
loop is `LinearSysDT.reach ... 1` iterated at a matrix that changes each time.

Nothing new is computed. `linearize` gives the system, `discretize` samples it
and `reach` takes the step; what re-linearizing costs is a fresh certificate per
step, which is data the caller supplies.

One step per linearization rather than a horizon per linearization. The sample
times are then the step boundaries, absolute time is `iΔt` and no partial sums
appear; reusing a linearization over several steps is the same recursion with
`reach ... K` and is left until something asks for it.

`Δt` and `o` are uniform, so `relinReach` recurses on the step index alone.

`exp` needs a norm on `Mat`, which is a choice rather than an instance, so this
file makes the same one as everything else reasoning about `discretize` — the
`l∞` operator norm — or the terms would not match.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S]

/-- The reachable set after `i` re-linearized steps of length `Δt`, from `R₀`
under the per-step input enclosures `Ud`, held at maximum order `o`. -/
noncomputable def NonlinearSys.relinReach (sys : NonlinearSys n m) {U : S m} (o : ℕ) (Δt : ℝ)
    (steps : ℕ → sys.LinStep U) (Ud : ℕ → S n) (R₀ : S n) : ℕ → S n
  | 0 => R₀
  | i + 1 => ((NonlinearSys.linearize (steps i).A).discretize Δt).reach o
      (sys.relinReach o Δt steps Ud R₀ i) (Ud i) 1

end CORALean.Real
