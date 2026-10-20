module

public import CORALean.ContDynamics.LinParamSys.Operations.DiscretizeEnclosure
public import CORALean.ContDynamics.LinParamSys.Theorems.IsConstTrajectoryToLinearSys
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntervalEnclosure
public import CORALean.ContDynamics.LinearSys.Operations.StepInput
public import CORALean.ContDynamics.LinearSys.Theorems.DiscretizeStep
public import CORALean.ContDynamics.LinearSys.Theorems.StepSubset
public import CORALean.ContSet.Interval.Real.Theorems.SmulOuter
public import CORALean.ContDynamics.LinearSys.Operations.Canonical

@[expose] public section

/-!
# A sampled constant-parameter run is a run of the discretized system

`LinearSys.IsCanonicalTrajectory.discretizeEnclosure` at `'constParam'`: one matrix `A` is fixed
over the whole run, so `toLinearSys` hands the sampled recursion to `discretize_step` unchanged,
and the witness each step needs is `exp_mem_expIntervalEnclosure` at that member of the box. The
discrete input is `LinearSys.stepInput` at the member, not a set-valued object of its own, which
is the reading `inputReach` already gets at `'constParam'`. `hε` is stated at the box, so it is
checkable before a member is fixed.

## Inputs
* `sys` – system
* `T` – time set
* `R₀` – initial set
* `U` – input set
* `Ud` – set of sampled inputs
* `x` – trajectory
* `u` – input signal
* `A` – system matrix member
* `Δt` – sampling time
* `η` – Taylor order

## Hypotheses
* `traj` – constant-parameter trajectory
* `hΔt` – sampling time nonnegative
* `hT` – nonnegative times lie in the time set
* `hU` – input set bounded
* `hUd` – sampled inputs lie in `Ud`
* `hε` – order admissible

## Conclusion
* the samples are a trajectory of the discretized system
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       12-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Sampling every `Δt` turns a `'constParam'` run into a run of the system the
exponential of the box discretizes to. -/
theorem LinParamSys.IsCanonicalConstTrajectory.discretizeEnclosure {sys : LinParamSys ℐ n}
    {T : Set ℝ}
    {R₀ U Ud : S n} {x u : ℝ → Vec ℝ n} {A : Mat ℝ n n} {Δt : ℝ} {η : ℕ}
    (traj : sys.IsCanonicalConstTrajectory T R₀ U x u A) (hΔt : 0 ≤ Δt) (hT : Set.Ici 0 ⊆ T)
    (hU : Bornology.IsBounded (construct U))
    (hUd : ∀ k : ℕ, (LinearSys.canonical A : LinearSys ℝ n).stepInput u Δt k ∈ construct Ud)
    (hε : ‖(Interval.smul Δt sys.A).absMax‖ / ((η : ℝ) + 2) < 1) :
    (sys.discretizeEnclosure Δt η).IsCanonicalTrajectory R₀ Ud
      (fun k : ℕ => x (k * Δt)) ((LinearSys.canonical A : LinearSys ℝ n).stepInput u Δt) where
  init := by simpa using traj.init
  input k := hUd k
  -- the member is the same matrix at every step; `LinParamSysDT` only permits it to vary
  step k := ⟨exp (Δt • A),
    MatExp.exp_mem_expIntervalEnclosure _ η
      (Interval.smul_outer Δt sys.A traj.param) hε, by
    simpa [LinParamSys.discretizeEnclosure, LinearSys.discretize, Scalar.toRealMat_real]
      using traj.toLinearSys.discretize_step hΔt hU k fun _ hs => hT hs.1⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
