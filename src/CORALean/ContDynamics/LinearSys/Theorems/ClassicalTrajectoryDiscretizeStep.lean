module

public import CORALean.ContDynamics.LinearSys.Operations.Discretize
public import CORALean.ContDynamics.LinearSys.Operations.StepInput
public import CORALean.ContDynamics.LinearSys.Theorems.ClassicalTrajectoryIntervalIntegrableInput
public import CORALean.ContDynamics.LinearSys.Theorems.ClassicalTrajectoryVariationOfConstants

@[expose] public section

/-!
# One step of the sampled recursion, for a classical run

Variation of constants over `[kΔt, (k+1)Δt]`, where the propagator is `e^{AΔt}`
whatever `k` is: every bounded-horizon statement is this iterated, so it is stated
apart from `discretize`, which needs every step at once. Kept for a classical run
on a window `[kΔt, (k+1)Δt]` that does not reach back to `0` — a nonlinear run
linearized step by step — where `ClassicalTrajectory.trajectory` cannot hand it to
`Trajectory`, whose integral equation is anchored at `0`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-August-2026
-- Last update:   10-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.ClassicalTrajectory.discretize_step {sys : LinearSys 𝕋 n} {T : Set ℝ}
    {R₀ U : S n} {x u : ℝ → Vec ℝ n} {Δt : ℝ} (traj : sys.ClassicalTrajectory T R₀ U x u)
    (hΔt : 0 ≤ Δt) (hU : Bornology.IsBounded (construct U)) (k : ℕ)
    (hT : Set.Icc ((k : ℝ) * Δt) (((k : ℝ) + 1) * Δt) ⊆ T) :
    x (((k : ℝ) + 1) * Δt)
      = toRealMat (sys.discretize Δt).A *ᵥ x ((k : ℝ) * Δt)
        + sys.stepInput u Δt k := by -- --- PROOF ---
  have hab : (k : ℝ) * Δt ≤ ((k : ℝ) + 1) * Δt := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have h := traj.variation_of_constants hT hab (traj.intervalIntegrable_input hT hab hU)
  have hstep : ((k : ℝ) + 1) * Δt - (k : ℝ) * Δt = Δt := by ring
  rw [hstep] at h
  simpa [LinearSys.discretize, LinearSys.stepInput] using h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
