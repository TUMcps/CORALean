module

public import CORALean.ContDynamics.LinearSys.Operations.Discretize
public import CORALean.ContDynamics.LinearSys.Operations.InputSolution
public import CORALean.ContDynamics.LinearSysDT.Operations.Reach
public import CORALean.ContDynamics.LinearSysDT.Operations.ReachOrders
public import CORALean.ContDynamics.LinearSysDT.Operations.ReachHeld
public import CORALean.ContDynamics.LinearSysDT.Operations.Simulate
public import CORALean.ContDynamics.NeurNetContrSys.Definitions.ReachOptions
public import CORALean.ContDynamics.NeurNetContrSys.NeurNetContrSys
public import CORALean.ContDynamics.Reach.Definitions.Params
public import CORALean.NN.Operations.Enclose

@[expose] public section

/-!
# The sampled loop: reachability at two rates

[1, Alg. 2]'s loop, at two nested levels — the whole point of the continuous
case. The outer recursion is on the control period: the network is invoked on
the enclosure reached at the end of the last period, and the input term it gives the plant,
`B N(R) ⊕ c`, is held. The inner level is `N` reachability steps of length `Δt`
under that one set, and it is `LinearSys`'s own machinery — `discretize`
samples the flow, `reach ... N` takes the steps, `inputSolution` encloses what
the input contributes to each.

`Δt` and `N` are separate options and the control period is `N Δt`. Nothing
new is computed, and only the period boundaries are reachable by this recursion,
the gap `relinReach` has.

Time is counted in control periods, `tStart` and `tFinal` being ℕ as in
`LinearSysDT.reach`: `Δt` is an ℝ that `discretize` needs, so no exact ℚ
quotient sets the period count. The count `tFinal - tStart` is exact, and every
guarantee is stated at `tStart = 0`.

## References

* [1] N. Kochdumper et al. "Open- and Closed-Loop Neural Network Verification
      using Polynomial Zonotopes". arXiv:2207.02715, 2022.
-/

-- Authors:       Claude Sonnet 5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S] [∀ n, OfPoint (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The reachable set at the end of `params.tFinal - params.tStart` control periods,
each `options.N` steps of length `options.Δt` under one held input set. -/
noncomputable def NeurNetContrSys.reach (sys : NeurNetContrSys 𝕋 S n)
    (params : Reach.Params (S n) ℕ) (options : NeurNetContrSys.ReachOptions ℝ) : S n :=
  let R₀ := params.X₀                                               -- the paper's symbols
  let Δt := options.Δt
  let N := options.N
  let η := options.η
  let o := options.ρ
  let H := params.tFinal - params.tStart                           -- control periods
  let period := fun R =>                                            -- N steps under one held input
    let U := Plus.plus (Mtimes.mtimes (𝕄 := Mat ℝ) (toRealMat sys.plant.B)
      (sys.contr.enclose R)) (OfPoint.ofPoint (toRealVec sys.plant.c))  -- B N(R) ⊕ c
    (sys.plant.discretize Δt).reach
      ⟨R, sys.plant.inputSolution Δt η U, 0, N⟩ ⟨o, options.hZonotopeOrder⟩
  Nat.rec (motive := fun _ => S n) R₀ (fun _ R => period R) H       -- R(HNΔt)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
