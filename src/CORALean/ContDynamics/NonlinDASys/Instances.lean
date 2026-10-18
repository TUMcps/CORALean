module

public import CORALean.ContDynamics.NonlinDASys.Theorems.ReachUnionOuter
public import CORALean.ContDynamics.Interfaces

@[expose] public section

/-!
# `NonlinDASys.WithSteps` instantiates `ContDynamics` and `Reach`

`params` and `options` are the reduced `NonlinearSys.WithSteps` run's own. `reachExact` is
`reachUnionExact` on `[0, tFinal - tStart]`, the states of the differential-algebraic system's
trajectories; `reach` is `reachUnion`, the reduced run; the guarantee is `reachUnion_outer`.
`reach` returns `none` exactly where the reduced run does.

`NonlinDASys` is a `ContDynamics`: `m` inputs and no disturbance, a run the state of a
`IsTrajectory` at some algebraic variable `y`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   15-October-2026
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
    Reach (NonlinDASys.WithSteps S Rg m p) (fun n _ => Reach.Params (S n) ℝ)
      (LinearSys.ReachOptions ℝ) S where
  reachExact sys params := sys.reachUnionExact (params.tFinal - params.tStart)
    (construct params.X₀)
  reach sys params options := sys.reachUnion params options
  reach_outer sys params options _ h := sys.reachUnion_outer params options _ h

/-- CORA's `nonlinDASys` as a `ContDynamics`: the state is `x`, `y` is carried by the run. -/
instance NonlinDASys.contDynamics {n p m : ℕ} : ContDynamics (NonlinDASys n p m) n where
  nrOfInputs _ := m
  nrOfDisturbances _ := 0
  IsTrajectory sys T X₀ U W x u w :=
    (∃ y, NonlinDASys.IsTrajectory (S := 𝒮) sys T X₀ U x y u
      (fun t => sys.h (x t) (y t) (u t))) ∧
      ∀ t ∈ T, w t ∈ W

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
