import CORALean.ContDynamics.LinearSys.Theorems.DiscretizeStep

/-!
# The run sampled from a bounded horizon alone

`discretize_step` iterated, each step at the prefix `[0, (k+1)Δt]` of the horizon. A
`TrajectoryOn K`, not a total `Trajectory` — nothing pins `x` or `u` past step
`K`, which is what lets `reach_outer_horizon` answer for a run over `[0, KΔt]`
without asking for all of forward time.
-/

-- Authors:       Claude Opus 5
-- Written:       18-August-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

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
  step k hk := by
    have hk' : ((k : ℝ) + 1) * Δt ≤ (K : ℝ) * Δt :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt hk) hΔt
    simpa using traj.discretize_step hΔt hU k ((Set.Icc_subset_Icc_right hk').trans hT)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
