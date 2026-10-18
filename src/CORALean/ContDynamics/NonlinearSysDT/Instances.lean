module

public import CORALean.ContDynamics.NonlinearSysDT.Theorems.ReachUnionOuter
public import CORALean.ContDynamics.Interfaces

@[expose] public section

/-!
# `NonlinearSysDT.WithSteps` instantiates `ContDynamicsDT` and `Reach`

`params` is `Reach.Params` counted in sampling periods, `options`
`NonlinearSysDT.ReachOptions`; `U` stays the system's, since each step's
certificate is issued for it. `reachExact` is `reachUnionExact` over
`tFinal - tStart` steps, the certificates counted from the run's start, `reach` is
`reachUnion`, and the guarantee is `reachUnion_outer`. `reach` can return `none`,
as `NonlinearSys`'s can: each step's linearization is trusted only once the set it
starts from is shown, at run time, inside that step's region, which is what lets
`reach_outer` hold with no confinement hypothesis on any run.

`NonlinearSysDT` is a `ContDynamicsDT`: every one of the `m` arguments of `f` an input, no
disturbance, a run a `IsTrajectory`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S Rg : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (Rg n) (Vec ℝ n)]
variable {m : ℕ}
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable {𝕋 : Type} [CORALean.Float.FloatOps 𝕋] [CORALean.Float.SoundFloatArithmetic 𝕋]
variable [Mtimes (Mat 𝕋) S] [CORALean.Float.OfInterval S 𝕋] [∀ n, Contains (Rg n) (S n)]


-- ========================================  INSTANCES  ========================================= --

instance NonlinearSysDT.reachInstance :
    Reach (NonlinearSysDT.WithSteps S Rg 𝕋 m) (fun n _ => Reach.Params (S n) ℕ)
      NonlinearSysDT.ReachOptions S where
  reachExact sys params := sys.reachUnionExact (params.tFinal - params.tStart)
    (construct params.X₀)
  reach sys params options := sys.reachUnion params options
  reach_outer sys params options _ h := sys.reachUnion_outer params options _ h

/-- CORA's `nonlinearSysDT` as a `ContDynamicsDT`: `x(k+1) = f(x(k), u(k))`. -/
instance NonlinearSysDT.contDynamicsDT {n m : ℕ} : ContDynamicsDT (NonlinearSysDT n m) n where
  nrOfInputs _ := m
  nrOfDisturbances _ := 0
  IsTrajectory sys X₀ U W x u w :=
    NonlinearSysDT.IsTrajectory (S := 𝒮) sys X₀ U x u ∧ ∀ k, w k ∈ W

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
