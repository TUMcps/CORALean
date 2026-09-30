import CORALean.ContDynamics.LinearSys.Operations.Discretize
import CORALean.ContDynamics.LinearSys.Operations.InputSolution
import CORALean.ContDynamics.LinearSysDT.Operations.Reach
import CORALean.ContDynamics.LinearSysDT.Operations.ReachOrders
import CORALean.ContDynamics.LinearSysDT.Operations.ReachHeld
import CORALean.ContDynamics.LinearSysDT.Operations.Simulate
import CORALean.ContDynamics.NeurNetContrSys.Definitions.ReachOptions
import CORALean.ContDynamics.NeurNetContrSys.NeurNetContrSys
import CORALean.ContDynamics.Reach.Definitions.Params
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

`timeStep` and `N` are separate options and the control period is `N Δt`. Nothing
new is computed, and only the period boundaries are reachable by this recursion,
the gap `relinReach` has.

Time is counted in control periods, `tStart` and `tFinal` being ℕ as in
`LinearSysDT.reach`: `timeStep` is an ℝ that `discretize` needs, so no exact ℚ
quotient sets the period count. The count `tFinal - tStart` is exact, and every
guarantee is stated at `tStart = 0`.

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

/-- The reachable set at the end of `params.tFinal - params.tStart` control periods,
each `options.N` steps of length `options.timeStep` under one held input set. -/
noncomputable def NeurNetContrSys.reach (sys : NeurNetContrSys 𝕋 S n)
    (params : Reach.Params (S n) ℕ) (options : NeurNetContrSys.ReachOptions) : S n :=
  let R₀ := params.R0                                               -- the paper's symbols
  let Δt := options.timeStep
  let N := options.N
  let η := options.taylorTerms
  let o := options.zonotopeOrder
  let H := params.tFinal - params.tStart                           -- control periods
  let period := fun R => (sys.plant.discretize Δt).reach          -- N steps under one held input
    ⟨R, sys.plant.inputSolution Δt η (sys.contr.enclose R), 0, N⟩ ⟨o, options.hZonotopeOrder⟩
  Nat.rec (motive := fun _ => S n) R₀ (fun _ R => period R) H       -- R(HNΔt)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
