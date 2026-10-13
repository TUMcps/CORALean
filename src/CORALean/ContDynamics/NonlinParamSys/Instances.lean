module

public import CORALean.ContDynamics.NonlinParamSys.Theorems.ReachUnionOuter
public import CORALean.ContDynamics.Reach.Reach

@[expose] public section

/-!
# `NonlinParamSys.WithSteps` instantiates `Reach`

`params` and `options` are the augmented `NonlinearSys.WithSteps` run's own,
`Reach.Params` at real time and `LinearSys.ReachOptions`, `X₀` lifted to `X₀ × P`
inside `reach`. `reachExact` is `reachUnionExact` on `[0, tFinal - tStart]`, the
constant-parameter reachable set; `reach` is `reachUnion`, the augmented-state run
projected back; the guarantee is `reachUnion_outer`. `reach` returns `none` exactly
where the augmented run does: a horizon no multiple of `Δt`, or some step's
start, inflated by `2MΔt`, not shown inside its region, tested in dimension `n + q`,
the parameter's coordinates with the state's. `ConvexSet` and `CompactSet` are asked
of the representation for the same reason as there.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open ContSet

variable {S Rg : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (Rg n) (Vec ℝ n)]
variable {m q : ℕ}
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [OfInterval S] [Mtimes ℐ S] [∀ n, Contains (Rg n) (S n)]
variable [∀ n, ConvexSet (S n) (Vec ℝ n)] [∀ n, CompactSet (S n) (Vec ℝ n)]


-- ========================================  INSTANCES  ========================================= --

noncomputable instance NonlinParamSys.reachInstance :
    Reach (NonlinParamSys.WithSteps S Rg m q) (fun n => Reach.Params (S n) ℝ)
      (LinearSys.ReachOptions ℝ) S where
  reachExact sys params := sys.reachUnionExact (params.tFinal - params.tStart)
    (construct params.X₀)
  reach sys params options := sys.reachUnion params options
  reach_outer sys params options := sys.reachUnion_outer params options

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
