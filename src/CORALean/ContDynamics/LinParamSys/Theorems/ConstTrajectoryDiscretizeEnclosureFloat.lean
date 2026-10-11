import CORALean.ContDynamics.LinParamSys.Operations.DiscretizeEnclosureFloat
import CORALean.ContDynamics.LinParamSys.Theorems.ConstTrajectoryToLinearSys
import CORALean.ContDynamics.LinParamSys.Theorems.ExpMemExpIntervalFloat
import CORALean.ContDynamics.LinearSys.Operations.StepInput
import CORALean.ContDynamics.LinearSys.Theorems.DiscretizeStep
import CORALean.ContDynamics.LinearSys.Theorems.StepSubset
import CORALean.ContSet.Interval.Float.Instances

/-!
# A sampled `'constParam'` run of the float-sampled system

`ConstTrajectory.discretizeEnclosure` with the float enclosure: `step` witnesses
the frozen member's `e^{AΔt}`, which lies in `[e^{AΔt}]` by
`exp_mem_expIntervalFloat` at an order admissible for `[Δt, Δt]`; sampling is at
the real time `toReal Δt` the float denotes.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


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
theorem LinParamSys.ConstTrajectory.discretizeEnclosureFloat
    {sys : LinParamSys (fun m n => Interval (Mat 𝕋 m n)) n} {T : Set ℝ}
    {R₀ U Ud : S n} {x u : ℝ → Vec ℝ n} {A : Mat ℝ n n} {Δt : 𝕋} {η : ℕ}
    (traj : sys.ConstTrajectory T R₀ U x u A) (hΔt : 0 ≤ toReal Δt) (hT : Set.Ici 0 ⊆ T)
    (hU : Bornology.IsBounded (construct U))
    (hUd : ∀ k : ℕ, (LinearSys.mk A : LinearSys ℝ n).stepInput u (toReal Δt) k ∈ construct Ud)
    (hη : sys.OrderAdmissibleFloat Δt Δt η) :
    (sys.discretizeEnclosureFloat Δt η).Trajectory R₀ Ud
      (fun k : ℕ => x (k * toReal Δt)) ((LinearSys.mk A : LinearSys ℝ n).stepInput u (toReal Δt))
    where
  init := by simpa using traj.init
  input k := hUd k
  -- the member is the same matrix at every step; `LinParamSysDT` only permits it to vary
  step k := ⟨exp (toReal Δt • A), sys.exp_mem_expIntervalFloat hη traj.param le_rfl le_rfl, by
    simpa [LinearSys.discretize, Scalar.toRealMat_real]
      using traj.toLinearSys.discretize_step hΔt hU k fun _ hs => hT hs.1⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
