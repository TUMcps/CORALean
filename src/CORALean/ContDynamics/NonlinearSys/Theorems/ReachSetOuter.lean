import CORALean.ContDynamics.NonlinearSys.Definitions.ReachSet

/-!
# `reachSet` contains every trajectory

The cheap half of the two-step form, exactly as in the linear case: a
trajectory is in the set of what trajectories reach by construction, so the
proof is the pair itself. All the content then sits in the other half, the
inclusion of this set in a computed one, where it reads as one set inside
another rather than as a claim about a run.

Stated at every `t`, including outside `T`: there `Trajectory` constrains
nothing beyond `x 0 ∈ R₀`, so the set is large and the theorems that consume it
ask for the window they speak about.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Reach for this to say where a run *is*; reach for a `reachSet_subset_`
theorem to say what encloses it. -/
theorem NonlinearSys.Trajectory.reachSet_outer {sys : NonlinearSys n m} {T : Set ℝ}
    {R₀ : S n} {U : S m} {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m}
    (traj : sys.Trajectory T R₀ U x u) (t : ℝ) :
    x t ∈ sys.reachSet T R₀ U t :=
  ⟨x, u, traj, rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
