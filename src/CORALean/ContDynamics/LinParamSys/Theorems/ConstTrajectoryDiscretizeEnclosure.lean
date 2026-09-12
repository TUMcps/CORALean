import CORALean.ContDynamics.LinParamSys.Operations.DiscretizeEnclosure
import CORALean.ContDynamics.LinParamSys.Theorems.ConstTrajectoryToLinearSys
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntervalEnclosure
import CORALean.ContDynamics.LinearSys.Operations.StepInput
import CORALean.ContDynamics.LinearSys.Theorems.DiscretizeStep
import CORALean.ContDynamics.LinearSys.Theorems.StepSubset
import CORALean.ContSet.Interval.Real.Theorems.SmulOuter

/-!
# A sampled constant-parameter run is a run of the discretized system

`LinearSys.Trajectory.discretizeEnclosure` at `'constParam'`: one matrix `A` is
fixed over the whole run, so `toLinearSys` hands the sampled recursion to
`discretize_step` unchanged, and the witness each step needs is
`exp_mem_expIntervalEnclosure` at that member of the box.

The discrete input is `LinearSys.stepInput` at the member, not a set-valued
object of its own, which is the reading `inputReach` already gets at
`'constParam'`: what one run's input contributed is a vector, and which matrix
propagated it is fixed by the run.

`hε` is stated at the box, so it is checkable before a member is fixed.
-/

-- Authors:       Tobias Ladner
-- Written:       12-September-2026
-- Last update:   ---
-- Last revision: ---


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
theorem LinParamSys.ConstTrajectory.discretizeEnclosure {sys : LinParamSys ℐ n} {T : Set ℝ}
    {R₀ U Ud : S n} {x u : ℝ → Vec ℝ n} {A : Mat ℝ n n} {Δt : ℝ} {η : ℕ}
    (traj : sys.ConstTrajectory T R₀ U x u A) (hΔt : 0 ≤ Δt) (hT : Set.Ici 0 ⊆ T)
    (hU : Bornology.IsBounded (construct U))
    (hUd : ∀ k : ℕ, (LinearSys.mk A : LinearSys ℝ n).stepInput u Δt k ∈ construct Ud)
    (hε : ‖(Interval.smul Δt sys.A).absMax‖ / ((η : ℝ) + 2) < 1) :
    (sys.discretizeEnclosure Δt η).Trajectory R₀ Ud
      (fun k : ℕ => x (k * Δt)) ((LinearSys.mk A : LinearSys ℝ n).stepInput u Δt) where
  init := by simpa using traj.init
  input k := hUd k
  -- the member is the same matrix at every step; `LinParamSysDT` only permits it to vary
  step k := ⟨exp (Δt • A),
    MatExp.exp_mem_expIntervalEnclosure _ η
      (Interval.smul_outer Δt sys.A traj.param) hε, by
    simpa [LinParamSys.discretizeEnclosure, LinearSys.discretize, Scalar.toRealMat_real]
      using traj.toLinearSys.discretize_step hΔt hU k (step_subset hΔt hT k)⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
