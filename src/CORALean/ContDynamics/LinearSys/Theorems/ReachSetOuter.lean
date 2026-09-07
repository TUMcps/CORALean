import CORALean.ContDynamics.LinearSys.ReachSet

/-!
# `reachSet` contains every trajectory

Half of the two-step form, and the cheap half: a trajectory is in the set of
what trajectories reach by construction, so the proof is the pair itself. That
is the point rather than a shortcoming — all the content of a reachability
claim then sits in the *other* half, the inclusion of this set in a computed
one, where it can be read as one set inside another.

Stated at every `t`, including outside `T`: there `Trajectory` constrains
nothing beyond `x 0 ∈ R₀`, so the set is large and the enclosure theorems that
consume it ask for the window they speak about.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Reach for this to say where a run *is*; reach for a `reachSet_subset_`
theorem to say what encloses it. -/
theorem LinearSys.Trajectory.reachSet_outer {sys : LinearSys 𝕋 n} {T : Set ℝ} {R₀ U : S n}
    {x u : ℝ → Vec ℝ n} (traj : sys.Trajectory T R₀ U x u) (t : ℝ) :
    x t ∈ sys.reachSet T R₀ U t :=
  ⟨x, u, traj, rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
