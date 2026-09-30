import CORALean.ContDynamics.LinearSys.Operations.Discretize
import CORALean.ContDynamics.LinearSys.Operations.InputSolution
import CORALean.ContDynamics.LinearSysDT.Operations.Reach
import CORALean.ContDynamics.LinearSysDT.Operations.ReachOrders
import CORALean.ContDynamics.LinearSysDT.Operations.ReachHeld
import CORALean.ContDynamics.LinearSysDT.Operations.Simulate
import CORALean.ContDynamics.NeurNetContrSys.NeurNetContrSys
import CORALean.NN.Operations.Enclose

/-!
# The sampled loop: reachability at two rates

[1, Alg. 2]'s loop, at two nested levels — the whole point of the continuous
case. The outer recursion is on the control period: the network is invoked on
the enclosure reached at the end of the last period, and the input set it
returns is held. The inner level is `N` reachability steps of length `Δt`
under that one set, and it is `LinearSys`'s own machinery — `discretize`
samples the flow, `reach ... N` takes the steps, `inputSolution` encloses what
the input contributes to each.

`Δt` and `N` are separate parameters and the control period is `N Δt`. Passing
`N = 1` recovers a controller running at the integrator's rate, the case that
does not arise in practice and the reason the two are not one parameter.

Nothing new is computed: every operation here was written for the open-loop
system, and the loop only chooses what to hand them. Only the period
boundaries are reachable by this recursion — covering the times inside one is
the same gap `relinReach` has.

## References

* [1] N. Kochdumper et al. "Open- and Closed-Loop Neural Network Verification
      using Polynomial Zonotopes". arXiv:2207.02715, 2022.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   30-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The reachable set at the end of `i` control periods, each `N` steps of
length `Δt` under one held input set, from `R₀`, at Taylor order `η` and
maximum order `o`. `ho` is what rules out `o = 0`. -/
noncomputable def NeurNetContrSys.reach (sys : NeurNetContrSys 𝕋 S n) (o η N : ℕ) (ho : 0 < o)
    (Δt : ℝ) (R₀ : S n) : ℕ → S n
  | 0 => R₀
  | i + 1 => (sys.plant.discretize Δt).reach
      ⟨sys.reach o η N ho Δt R₀ i,
        sys.plant.inputSolution Δt η (sys.contr.enclose (sys.reach o η N ho Δt R₀ i)), 0, N⟩ ⟨o, ho⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
