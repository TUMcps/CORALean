import CORALean.ContDynamics.NonlinearSysDT.Theorems.ReachUnionOuter
import CORALean.ContDynamics.Reach.Reach

/-!
# `NonlinearSysDT.WithSteps` instantiates `Reach`

`params` is `Reach.Params` counted in sampling periods, `options`
`NonlinearSysDT.ReachOptions`; `U` stays the system's, since each step's
certificate is issued for it. `reachExact` is `reachUnionExact` over
`tFinal - tStart` steps, the certificates counted from the run's start, `reach` is
`reachUnion`, and the guarantee is `reachUnion_outer`. `reach` can return `none`,
as `NonlinearSys`'s can: each step's linearization is trusted only once the set it
starts from is shown, at run time, inside that step's region, which is what lets
`reach_outer` hold with no confinement hypothesis on any run.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   30-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S Rg : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (Rg n) (Vec ℝ n)]
variable {m : ℕ}
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Real.OfInterval S] [∀ n, Contains (Rg n) (S n)]


-- ========================================  INSTANCES  ========================================= --

instance NonlinearSysDT.reachInstance :
    Reach (NonlinearSysDT.WithSteps S Rg m) (fun n => Reach.Params (S n) ℕ)
      NonlinearSysDT.ReachOptions S where
  reachExact sys params := sys.reachUnionExact (params.tFinal - params.tStart)
    (construct params.R0)
  reach sys params options := sys.reachUnion params options
  reach_outer sys params options := sys.reachUnion_outer params options

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
