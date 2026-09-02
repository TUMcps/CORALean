import CORALean.ContDynamics.LinearSys.Operations.Discretize
import CORALean.ContDynamics.LinearSys.Operations.InputSolution
import CORALean.ContDynamics.LinearSysDT.Operations
import CORALean.ContDynamics.NeurNetContrSys.NeurNetContrSys
import CORALean.NN.Operations.Propagate

/-!
# The sampled loop: reachability at two rates

Two nested levels, which is the whole point of the continuous case. The outer
recursion is on the control period: the network is invoked on the enclosure
reached at the end of the last period, and the input set it returns is held.
The inner level is `N` reachability steps of length `Δt` under that one set, and
it is `LinearSys`'s own machinery — `discretize` samples the flow, `reach ... N`
takes the steps, `inputSolution` encloses what the input contributes to each.

`Δt` and `N` are separate parameters and the control period is `N Δt`. Passing
`N = 1` recovers a controller running at the integrator's rate, which is the
case that does not arise in practice and is why the two are not one parameter.

Nothing new is computed, again: every operation called here was written for the
open-loop system, and the loop only chooses what to hand them.

Sample times of the *inner* grid are what `reach` speaks about, but only the
period boundaries are reachable by this recursion, since only there does an
enclosure exist to hand the network. Covering the times inside a period is
`timeIntervalStep` per step, and it is not here — the same gap `relinReach` has.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S]

/-- The reachable set at the end of `i` control periods, each `N` steps of
length `Δt` under one held input set, from `R₀`, at Taylor order `η` and
maximum order `o`. -/
noncomputable def NeurNetContrSys.reach (sys : NeurNetContrSys 𝕋 S n) (o η N : ℕ) (Δt : ℝ)
    (R₀ : S n) : ℕ → S n
  | 0 => R₀
  | i + 1 => (sys.plant.discretize Δt).reach o (sys.reach o η N Δt R₀ i)
      (sys.plant.inputSolution Δt η (sys.contr.propagate (sys.reach o η N Δt R₀ i))) N

end CORALean.Real
