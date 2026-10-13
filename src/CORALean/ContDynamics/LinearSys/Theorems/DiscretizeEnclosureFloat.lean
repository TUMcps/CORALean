module

public import CORALean.ContDynamics.LinearSys.Operations.DiscretizeEnclosureFloat
public import CORALean.ContDynamics.LinearSys.Theorems.DiscretizeStep
public import CORALean.ContDynamics.LinearSys.Theorems.ExpMemExpIntervalFloat
public import CORALean.ContDynamics.LinearSys.Theorems.StepSubset
public import CORALean.ContSet.Interval.Float.Instances

@[expose] public section

/-!
# A sampled trajectory of the float-enclosed system

`discretizeEnclosure`'s `Trajectory` with the float enclosure in place of the
real one: `step` witnesses the exact `e^{AΔt}`, which lies in `[e^{AΔt}]` by
`exp_mem_expIntervalFloat` at an order admissible for `[Δt, Δt]`. The sampling
is the exact one, at the real time `toReal Δt` the float denotes.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
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

/-- A run of `sys`, sampled at `toReal Δt`, is a run of the float-sampled system. -/
theorem LinearSys.Trajectory.discretizeEnclosureFloat {sys : LinearSys 𝕋 n} {T : Set ℝ}
    {R₀ U Ud : S n} {x u : ℝ → Vec ℝ n} {Δt : 𝕋} {η : ℕ}
    (traj : sys.Trajectory T R₀ U x u) (hΔt : 0 ≤ toReal Δt) (hT : Set.Ici 0 ⊆ T)
    (hU : Bornology.IsBounded (construct U))
    (hUd : ∀ k : ℕ, sys.stepInput u (toReal Δt) k ∈ construct Ud)
    (hη : sys.OrderAdmissibleFloat Δt Δt η) :
    (sys.discretizeEnclosureFloat Δt η).Trajectory R₀ Ud
      (fun k : ℕ => x (k * toReal Δt)) (sys.stepInput u (toReal Δt)) where
  init := by simpa using traj.init
  input k := hUd k
  step k := ⟨exp (toReal Δt • Scalar.toRealMat sys.A),
    sys.exp_mem_expIntervalFloat hη le_rfl le_rfl, by
    simpa [LinearSys.discretize] using traj.discretize_step hΔt hU k fun _ hs => hT hs.1⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
