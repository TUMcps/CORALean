module

public import CORALean.ContDynamics.LinParamSysDT.Theorems.ReachOuterOn
public import CORALean.ContDynamics.LinearSys.Operations.DiscretizeEnclosureFloat
public import CORALean.ContDynamics.LinearSys.Theorems.DiscretizeHorizon
public import CORALean.ContDynamics.LinearSys.Theorems.ExpMemExpIntervalFloat
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachSubsetInputSolutionFloat
public import CORALean.ContDynamics.LinearSys.Theorems.StepInputMemInputReach
public import CORALean.ContDynamics.LinearSys.Theorems.StepSubsetHorizon

@[expose] public section

/-!
# The float-sampled `reach` contains a run over a bounded horizon, inputs and all

`reach_outer_horizon_inputSolution` in floats: the run sampled at `toReal Δt` is a
run of `discretizeEnclosureFloat` for its first `K` steps, `e^{AΔt}` lying in the
float box, and each step's input contribution lies in `inputSolutionFloat U`,
being one admissible input's contribution (`stepInput_mem_inputReach`). Only the
steps inside the horizon are spoken about.
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


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every sample `x (k Δt)`, `k ≤ K`, of a run on `[0, K Δt]` lies in the float-sampled
system's `reach` under the float input solution of `U`. -/
theorem LinearSys.IsCanonicalTrajectory.discretizeEnclosureFloat_mem_reach_horizon
    {sys : LinearSys 𝕋 n}
    {T : Set ℝ} {R₀ U : Zonotope (Vec 𝕋 n)} {x u : ℝ → Vec ℝ n} {Δt : 𝕋} {η K : ℕ}
    (traj : sys.IsCanonicalTrajectory (S := 𝒵[𝕋]) T R₀ U x u) (hΔt : 0 < toReal Δt)
    (hT : Set.Icc 0 ((K : ℝ) * toReal Δt) ⊆ T) (hη : sys.OrderAdmissibleFloat Δt Δt η)
    {o : ℕ} (ho : 0 < o) : -- --- STMT ---
    ∀ k ≤ K, x ((k : ℝ) * toReal Δt) ∈ construct
    ((sys.discretizeEnclosureFloat Δt η).reach (S := 𝒵[𝕋])
      ⟨R₀, sys.inputSolutionFloat Δt η U, 0, k⟩ ⟨o, ho⟩) := by -- --- PROOF ---
  -- the exact sampling, every step's input inside the float input solution
  have hdt := traj.discretize_horizon (Ud := sys.inputSolutionFloat Δt η U) hΔt.le hT
    (CompactSet.isBounded_construct U) fun j hj =>
      sys.inputReach_subset_inputSolutionFloat hΔt hη U
        (traj.stepInput_mem_inputReach j (step_subset_horizon hΔt.le hT hj))
  -- the same run, its matrix only enclosed
  have hon : (sys.discretizeEnclosureFloat Δt η).IsCanonicalTrajectoryOn (S := 𝒵[𝕋]) R₀
    (sys.inputSolutionFloat Δt η U) K
      (fun k : ℕ => x (k * toReal Δt)) (sys.stepInput u (toReal Δt)) :=
    { init := hdt.init
      input := hdt.input
      step := fun j hj => ⟨exp (toReal Δt • Scalar.toRealMat sys.A),
        sys.exp_mem_expIntervalFloat hη le_rfl le_rfl, by
          simpa [LinearSys.discretize] using hdt.step j hj⟩ }
  exact fun k hk => (sys.discretizeEnclosureFloat Δt η).reach_outer_on
    (S := 𝒵[𝕋]) ho R₀ _ hon k hk

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
