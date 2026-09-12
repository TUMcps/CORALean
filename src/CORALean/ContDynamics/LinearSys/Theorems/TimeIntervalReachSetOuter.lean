import CORALean.ContDynamics.LinearSys.TimeIntervalReachSet

/-!
# `timeIntervalReachSet` contains every trajectory over the interval

The cheap half, as `ReachSetOuter` is for `reachSet`: a trajectory at any time
of `[0, r]` is in the set of what trajectories reach over `[0, r]` by
construction.
-/

-- Authors:       Tobias Ladner
-- Written:       11-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Reach for this to say where a run is over the whole interval; reach for
`timeIntervalReachSet_eq_iUnion` to read it as a union of `reachSet`. -/
theorem LinearSys.Trajectory.timeIntervalReachSet_outer {sys : LinearSys 𝕋 n} {T : Set ℝ}
    {R₀ U : S n} {x u : ℝ → Vec ℝ n} (traj : sys.Trajectory T R₀ U x u) {r t : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) r) :
    x t ∈ sys.timeIntervalReachSet T R₀ U r :=
  ⟨x, u, traj, t, ht, rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
