module

public import CORALean.ContDynamics.NonlinParamSys.Theorems.ReachUnionOuter
public import CORALean.ContDynamics.Interfaces

@[expose] public section

/-!
# `NonlinParamSys.WithSteps` instantiates `ContDynamics` and `Reach`

`params` and `options` are the augmented `NonlinearSys.WithSteps` run's own, `X₀` lifted to
`X₀ × P` inside `reach`. `reachExact` is `reachUnionExact` on `[0, tFinal - tStart]`, the
constant-parameter reachable set; `reach` is `reachUnion`, the augmented-state run projected
back; the guarantee is `reachUnion_outer`. `reach` returns `none` exactly where the augmented
run does, tested in dimension `n + q`. `NonlinParamSys` is a `ContDynamics`: `m` inputs, and
the `q` parameters as the disturbance, a fresh `p t` in the parameter set at every instant, as
`IsTrajectory` reads them.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   15-October-2026
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
    Reach (NonlinParamSys.WithSteps S Rg m q) (fun n _ => Reach.Params (S n) ℝ)
      (LinearSys.ReachOptions ℝ) S where
  reachExact sys params := sys.reachUnionExact (params.tFinal - params.tStart)
    (construct params.X₀)
  reach sys params options := sys.reachUnion params options
  reach_outer sys params options _ h := sys.reachUnion_outer params options _ h

/-- CORA's `nonlinParamSys` as a `ContDynamics`: `ẋ = f(x, u, p)`, `p` the disturbance. -/
instance NonlinParamSys.contDynamics {n m q : ℕ} : ContDynamics (NonlinParamSys n m q) n where
  nrOfInputs _ := m
  nrOfDisturbances _ := q
  IsTrajectory sys T X₀ U W x u w :=
    NonlinParamSys.IsTrajectory (S := 𝒮) sys T X₀ U W x u w (fun t => sys.g (x t) (u t) (w t))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
