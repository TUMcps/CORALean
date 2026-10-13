import CORALean.ContDynamics.LinearSys.Theorems.FlowIci

/-!
# A classical run's input as a derivative, drift subtracted

`u` as a derivative minus the drift. The flow states the sum; this is the
rearrangement that leaves `u` alone on one side, which is what carries
measurability to a classical run's `u` on a window `[a, b]` that need not reach
back to `0` — where `ClassicalTrajectory.trajectory` cannot hand the run to
`Trajectory`, whose integral equation is anchored there.
-/

-- Authors:       Claude Opus 5
-- Written:       19-August-2026
-- Last update:   10-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.ClassicalTrajectory.input_eq_derivWithin {sys : LinearSys 𝕋 n}
    {T : Set ℝ} {R₀ U : S n} {x u : ℝ → Vec ℝ n} (traj : sys.ClassicalTrajectory T R₀ U x u)
    {a b t : ℝ} (hT : Set.Icc a b ⊆ T) (ht : t ∈ Set.Ico a b) :
    u t = derivWithin x (Set.Ici t) t - toRealMat sys.A *ᵥ x t := by
  rw [(traj.flow_Ici hT ht).derivWithin (uniqueDiffWithinAt_Ici t)]
  abel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
