module

public import CORALean.ContDynamics.NonlinearSys.Definitions.ReachSetExact

@[expose] public section

/-!
# `reachSetExact` contains every trajectory

The cheap half of the two-step form, exactly as in the linear case: a
trajectory is in the set of what trajectories reach by construction, so the
proof is the pair itself. All the content then sits in the other half, the
inclusion of this set in a computed one, where it reads as one set inside
another rather than as a claim about a run.

Stated at every `t`, including outside `T`: there `IsTrajectory` constrains
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

/-- Reach for this to say where a run *is*; reach for a `reachSetExact_subset_`
theorem to say what encloses it. -/
theorem NonlinearSys.IsTrajectory.reachSetExact_outer {sys : NonlinearSys n m} {T : Set ℝ}
    {R₀ : S n} {U : S m} {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m} {y : ℝ → Vec ℝ sys.q}
    (traj : sys.IsTrajectory T R₀ U x u y) (t : ℝ) :
    x t ∈ sys.reachSetExact T R₀ U t :=
  -- the output is read off the run, the same at every point of `T`
  ⟨x, u, { traj with output := fun _ _ => rfl }, rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
