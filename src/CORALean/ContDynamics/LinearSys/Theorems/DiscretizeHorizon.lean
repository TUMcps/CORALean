import CORALean.ContDynamics.LinearSys.Theorems.DiscretizeStep
import CORALean.ContDynamics.LinearSys.Theorems.StepSubsetHorizon

/-!
# The run sampled from a bounded horizon alone

`discretize_step` iterated, at the domain `step_subset_horizon` carves out. A
`TrajectoryOn K`, not a total `Trajectory` — nothing pins `x` or `u` past step
`K`, which is what lets `reach_outer_horizon` answer for a run over `[0, KΔt]`
without asking for all of forward time.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.Trajectory.discretize_horizon {sys : LinearSys 𝕋 n} {T : Set ℝ}
    {R₀ U Ud : S n} {x u : ℝ → Vec ℝ n} {Δt : ℝ} {K : ℕ}
    (traj : sys.Trajectory T R₀ U x u) (hΔt : 0 ≤ Δt)
    (hT : Set.Icc 0 ((K : ℝ) * Δt) ⊆ T) (hU : Bornology.IsBounded (construct U))
    (hUd : ∀ k < K, sys.stepInput u Δt k ∈ construct Ud) :
    (sys.discretize Δt).TrajectoryOn R₀ Ud K
      (fun k : ℕ => x (k * Δt)) (sys.stepInput u Δt) where
  init := by simpa using traj.init
  input k hk := hUd k hk
  step k hk := by simpa using traj.discretize_step hΔt hU k (step_subset_horizon hΔt hT hk)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
