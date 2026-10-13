import CORALean.ContDynamics.NonlinDASys.Theorems.ReachUnionOuter
import CORALean.ContDynamics.Reach.Reach

/-!
# `NonlinDASys.WithSteps` instantiates `Reach`

`params` and `options` are the reduced `NonlinearSys.WithSteps` run's own. `reachExact` is
`reachUnionExact` on `[0, tFinal - tStart]`, the states of the differential-algebraic system's
trajectories; `reach` is `reachUnion`, the reduced run; the guarantee is `reachUnion_outer`.
`reach` returns `none` exactly where the reduced run does.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open ContSet

variable {S Rg : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (Rg n) (Vec ℝ n)]
variable {m p : ℕ}
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [OfInterval S] [Mtimes ℐ S] [∀ n, Contains (Rg n) (S n)]
variable [∀ n, ConvexSet (S n) (Vec ℝ n)] [∀ n, CompactSet (S n) (Vec ℝ n)]


-- ========================================  INSTANCES  ========================================= --

noncomputable instance NonlinDASys.reachInstance :
    Reach (NonlinDASys.WithSteps S Rg m p) (fun n => Reach.Params (S n) ℝ)
      (LinearSys.ReachOptions ℝ) S where
  reachExact sys params := sys.reachUnionExact (params.tFinal - params.tStart)
    (construct params.X₀)
  reach sys params options := sys.reachUnion params options
  reach_outer sys params options := sys.reachUnion_outer params options

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
