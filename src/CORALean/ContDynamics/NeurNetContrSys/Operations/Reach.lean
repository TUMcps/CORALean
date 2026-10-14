module

public import CORALean.ContDynamics.LinearSys.Operations.Discretize
public import CORALean.ContDynamics.LinearSys.Operations.InputSolution
public import CORALean.ContDynamics.LinearSysDT.Operations.Reach
public import CORALean.ContDynamics.NeurNetContrSys.Definitions.ReachOptions
public import CORALean.ContDynamics.NeurNetContrSys.Operations.Augment
public import CORALean.ContDynamics.NeurNetContrSys.Operations.CartProd
public import CORALean.ContDynamics.NeurNetContrSys.Operations.Project
public import CORALean.ContDynamics.NeurNetContrSys.Operations.ReachWith
public import CORALean.ContDynamics.Reach.Definitions.Params

@[expose] public section

/-!
# The sampled loop at a linear plant: reachability at two rates

[1, Alg. 2] (`reachWith`) at a `LinearSys` plant, CORA's `neurNetContrSys/reach` with
`aux_reachability` choosing `linearSys`'s own. The outer recursion is on the control period:
the network's image `Y` of the set reached so far is stacked under it (`cartProd`, CORA's
`aux_appendU2X`), the pair reached as one state of the augmented system `[A B; 0 0]`, `[c; 0]`
(`augment`, CORA's `aux_augmentLinear`) and projected back (`project`). The inner level is `N`
steps of length `Δt` of that system by `LinearSys`'s own machinery: `discretize`, `reach ... N`,
and `inputSolution` of the constant `[c; 0]`.

The input is a state, so its constancy over the period is kept and the same input acts at all
`N` steps; only the dependence of `Y` on the state is lost, the product being the plain one.
Only the period boundaries are reached (`rx` returns no sets over a period), the gap
`relinReach` has. Time is counted in control periods, `tStart` and `tFinal` being ℕ as in
`LinearSysDT.reach`; every guarantee is stated at `tStart = 0`.

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
open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S] [∀ n, OfPoint (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The reachable set at the end of `params.tFinal - params.tStart` control periods, each
`options.N` steps of length `options.Δt` of the augmented system from the state set stacked over
the network's image. -/
noncomputable def NeurNetContrSys.reach (sys : NeurNetContrSys (LinearSys 𝕋 n) S n)
    (params : Reach.Params (S n) ℕ) (options : NeurNetContrSys.ReachOptions ℝ) : S n :=
  let R₀ := params.X₀                                               -- the paper's symbols
  let Δt := options.Δt
  let N := options.N
  let η := options.η
  let o := options.ρ
  let H := params.tFinal - params.tStart                           -- control periods
  let ext := sys.augment                                            -- [A B; 0 0], [c; 0]
  let rx := fun Z =>                                                -- N steps of ext from Z
    ((ext.discretize Δt).reach ⟨Z, ext.inputSolution Δt η (OfPoint.ofPoint ext.c), 0, N⟩
      ⟨o, options.hZonotopeOrder⟩, [])
  (sys.reachWith NeurNetContrSys.cartProd NeurNetContrSys.project rx R₀ H).1  -- R(HNΔt)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
