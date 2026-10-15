module

public import CORALean.ContDynamics.NonlinearSys.Theorems.ReachUnionOuter
public import CORALean.ContDynamics.Interfaces

@[expose] public section

/-!
# `NonlinearSys.WithSteps` instantiates `ContDynamics` and `Reach`

`params` is `Reach.Params` at real time, `options` `LinearSys.ReachOptions` — each
step is a linear one, and CORA's `nonlinearSys` reads the same `timeStep`,
`taylorTerms` and `zonotopeOrder`. `U` stays the system's, since each step's
certificate is issued for it. `reachExact` is `reachUnionExact` on
`[0, tFinal - tStart]`, the certificates counted from the run's start, `reach` is
`reachUnion`, and the guarantee is `reachUnion_outer`. `reach` returns `none` where
the horizon is no multiple of `Δt`, or a step's linearization could not be
trusted: the set it starts from, inflated by `2MΔt`, not shown inside its region
at run time. That test is what lets `reach_outer` hold with no confinement
hypothesis on any run. `ConvexSet` and `CompactSet` are asked of the
representation, as `NeurNetContrSys`'s instance asks them, and discharge every side
condition the linear step would otherwise put in `options`.

`NonlinearSys` is a `ContDynamics`: every one of the `m` arguments of `f` an input, no
disturbance, a run a `Trajectory`.
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
variable {m : ℕ}
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [OfInterval S] [Mtimes ℐ S] [∀ n, Contains (Rg n) (S n)]
variable [∀ n, ConvexSet (S n) (Vec ℝ n)] [∀ n, CompactSet (S n) (Vec ℝ n)]


-- ========================================  INSTANCES  ========================================= --

noncomputable instance NonlinearSys.reachInstance :
    Reach (NonlinearSys.WithSteps S Rg m) (fun n _ => Reach.Params (S n) ℝ)
      (LinearSys.ReachOptions ℝ) S where
  reachExact sys params := sys.reachUnionExact (params.tFinal - params.tStart)
    (construct params.X₀)
  reach sys params options := sys.reachUnion params options
  reach_outer sys params options _ h := sys.reachUnion_outer params options h

/-- CORA's `nonlinearSys` as a `ContDynamics`: `ẋ = f(x, u)`. -/
instance NonlinearSys.contDynamics {n m : ℕ} : ContDynamics (NonlinearSys n m) n where
  nrOfInputs _ := m
  nrOfDisturbances _ := 0
  Trajectory sys T X₀ U W x u w :=
    NonlinearSys.Trajectory (S := 𝒮) sys T X₀ U x u ∧ ∀ t ∈ T, w t ∈ W

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
