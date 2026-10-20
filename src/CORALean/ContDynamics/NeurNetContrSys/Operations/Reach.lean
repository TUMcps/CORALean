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

[1, Alg. 2] (`reachWith`) at a `LinearSys` plant, CORA's `neurNetContrSys/reach`. The outer
recursion is on the control period: the network's image `Y` of the set reached so far is stacked
under it (`cartProd`), the pair reached as one state of the augmented system (`augment`) and
projected back (`project`). The inner level is `N` steps of length `Δt` of that system by
`LinearSys`'s own machinery (`discretize`, `reach`, `inputSolution` of `B_aug U_ext ⊕ [c; 0]`).
The network's input is a state, so its constancy over the period is kept; only the dependence of
`Y` on the state is lost. Only the period boundaries are reached; `tStart`, `tFinal` are ℕ, in
control periods, and every guarantee is stated at `tStart = 0`.

## Inputs
* `sys` – closed-loop system
* `U_ext` – external input set
* `params` – reachability parameters
* `options` – reachability options

## Output
* the reachable set at the end of the last control period

## References

* [1] N. Kochdumper et al. "Open- and Closed-Loop Neural Network Verification
      using Polynomial Zonotopes". arXiv:2207.02715, 2022.
-/

-- Authors:       Claude Sonnet 5, Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       02-September-2026
-- Last update:   15-October-2026
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
the network's image, under the external inputs `U_ext`. -/
noncomputable def NeurNetContrSys.reach (sys : NeurNetContrSys (LinearSys 𝕋 n) S n)
    (U_ext : S sys.nExt) (params : Reach.Params (S n) ℕ)
    (options : NeurNetContrSys.ReachOptions ℝ) : S n :=
  let R₀ := params.X₀                                               -- the paper's symbols
  let Δt := options.Δt
  let N := options.N
  let η := options.η
  let o := options.ρ
  let H := params.tFinal - params.tStart                           -- control periods
  let ext := sys.augment                                            -- [A B_nn; 0 0], [B_ext; 0]
  let U := Plus.plus (Mtimes.mtimes (𝕄 := Mat ℝ) ext.B U_ext)      -- B_aug U_ext ⊕ [c; 0]
    (OfPoint.ofPoint ext.c)
  let rx := fun Z =>                                                -- N steps of ext from Z
    ((ext.discretize Δt).reach ⟨Z, ext.inputSolution Δt η U, 0, N⟩
      ⟨o, options.hZonotopeOrder⟩, [])
  (sys.reachWith NeurNetContrSys.cartProd NeurNetContrSys.project rx R₀ H).1  -- R(HNΔt)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
