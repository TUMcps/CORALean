module

public import CORALean.ContDynamics.LinParamSys.Operations.DiscretizeEnclosureFloat
public import CORALean.ContDynamics.LinParamSys.Theorems.IsConstTrajectoryToLinearSys
public import CORALean.ContDynamics.LinParamSys.Theorems.ExpMemExpIntervalFloat
public import CORALean.ContDynamics.LinearSys.Operations.StepInput
public import CORALean.ContDynamics.LinearSys.Theorems.DiscretizeStep
public import CORALean.ContDynamics.LinearSys.LinearSys
public import CORALean.ContSet.Interval.Float.Instances
public import CORALean.ContDynamics.LinearSys.Operations.Canonical

@[expose] public section

/-!
# A sampled `'constParam'` run of the float-sampled system

`IsCanonicalConstTrajectory.discretizeEnclosure` with the float enclosure: `step` witnesses
the frozen member's `e^{AΔt}`, which lies in `[e^{AΔt}]` by
`exp_mem_expIntervalFloat` at an order admissible for `[Δt, Δt]`; sampling is at
the real time `toReal Δt` the float denotes.

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
* `hη` – order admissible

## Conclusion
* the samples are a trajectory of the float-sampled system
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       01-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic
open Matrix ContSet NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Sampling every `Δt` turns a `'constParam'` run into a run of the float-sampled
system. -/
theorem LinParamSys.IsCanonicalConstTrajectory.discretizeEnclosureFloat
    {sys : LinParamSys ℐ[𝕋] n} {T : Set ℝ}
    {R₀ U Ud : S n} {x u : ℝ → Vec ℝ n} {A : Mat ℝ n n} {Δt : 𝕋} {η : ℕ}
    (traj : sys.IsCanonicalConstTrajectory T R₀ U x u A) (hΔt : 0 ≤ toReal Δt) (hT : Set.Ici 0 ⊆ T)
    (hU : Bornology.IsBounded (construct U))
    (hUd : ∀ k : ℕ, (LinearSys.canonical A : LinearSys ℝ n).stepInput u (toReal Δt) k ∈ construct
        Ud)
    (hη : sys.IsOrderAdmissibleFloat Δt Δt η) :
    (sys.discretizeEnclosureFloat Δt η).IsCanonicalTrajectory R₀ Ud
      (fun k : ℕ => x (k * toReal Δt))
          ((LinearSys.canonical A : LinearSys ℝ n).stepInput u (toReal Δt))
    where
  init := by simpa using traj.init
  input k := hUd k
  -- the member is the same matrix at every step; `LinParamSysDT` only permits it to vary
  step k := ⟨exp (toReal Δt • A), sys.exp_mem_expIntervalFloat hη traj.param le_rfl le_rfl, by
    simpa [LinearSys.discretize, Scalar.toRealMat_real]
      using traj.toLinearSys.discretize_step hΔt hU k fun _ hs => hT hs.1⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
