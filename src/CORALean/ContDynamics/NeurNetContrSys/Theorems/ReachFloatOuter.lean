module

public import CORALean.ContDynamics.LinearSys.Theorems.ClassicalTrajectoryTrajectory
public import CORALean.ContDynamics.LinearSys.Theorems.DiscretizeEnclosureFloatHorizon
public import CORALean.ContDynamics.NeurNetContrSys.Operations.ReachFloat
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.Period
public import CORALean.ContSet.ContSet.Theorems.Basic

@[expose] public section

/-!
# `NeurNetContrSys.reachFloat` contains every sampled run at the period boundaries

`reach_outer` in floats: an induction on the control period whose step is
`Trajectory.period`, the period read as a linear run under the enclosed input
set, handed to `discretizeEnclosureFloat_mem_reach_horizon` for `N` steps. The
control period is `N` times the real time `toReal Δt` the float step denotes.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic
open Matrix ContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every zero-order-hold run of `H` control periods is inside `reachFloat` at every
period boundary, the order admissible for the step. -/
theorem NeurNetContrSys.reachFloat_outer (sys : NeurNetContrSys 𝕋 𝒵[𝕋] n)
    (o η N : ℕ) (ho : 0 < o) {Δt : 𝕋} (hΔt : 0 < toReal Δt)
    (hη : sys.plant.OrderAdmissibleFloat Δt Δt η) {H : ℕ} {R₀ : Zonotope (Vec 𝕋 n)}
    {π : Vec ℝ n → Vec ℝ n} (hπ : sys.contr.Sound π) {x : ℝ → Vec ℝ n}
    (traj : sys.Trajectory π ((N : ℝ) * toReal Δt) H R₀ x) :
    ∀ i ≤ H, x ((i : ℝ) * ((N : ℝ) * toReal Δt)) ∈
      construct (sys.reachFloat ⟨R₀, 0, i⟩ ⟨Δt, N, η, o, ho⟩) := by -- --- PROOF ---
  intro i
  -- the induction is on the control period, `traj.period` being its step
  induction i with
  | zero =>
    intro _
    show x (((0 : ℕ) : ℝ) * ((N : ℝ) * toReal Δt)) ∈ construct R₀
    simpa using traj.init
  | succ i ih =>
    intro hi
    have hiH : i < H := Nat.lt_of_succ_le hi
    have hNΔ : (0:ℝ) ≤ (N : ℝ) * toReal Δt := mul_nonneg (Nat.cast_nonneg N) hΔt.le
    have key := ((traj.period hπ i hiH _ (ih hiH.le)).trajectory (convex_Icc 0 _)
      ⟨le_rfl, hNΔ⟩ (CompactSet.isBounded_construct _)).discretizeEnclosureFloat_mem_reach_horizon
      (K := N) hΔt subset_rfl hη ho N le_rfl
    -- the conclusion unfolded, so `key` matches it at the period's own clock
    show x (((i + 1 : ℕ) : ℝ) * ((N : ℝ) * toReal Δt)) ∈ construct
      ((sys.plant.discretizeEnclosureFloat Δt η).reach (S := 𝒵[𝕋])
        ⟨sys.reachFloat ⟨R₀, 0, i⟩ ⟨Δt, N, η, o, ho⟩,
          sys.plant.inputSolutionFloat Δt η
            (sys.contr.enclose (sys.reachFloat ⟨R₀, 0, i⟩ ⟨Δt, N, η, o, ho⟩)), 0, N⟩ ⟨o, ho⟩)
    rw [show ((i + 1 : ℕ) : ℝ) * ((N : ℝ) * toReal Δt)
      = (i : ℝ) * ((N : ℝ) * toReal Δt) + (N : ℝ) * toReal Δt from by push_cast; ring]
    exact key

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
