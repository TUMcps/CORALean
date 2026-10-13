module

public import CORALean.ContDynamics.NeurNetContrSys.Definitions.ReachSet

@[expose] public section

/-!
# `reachSet` contains every sampled run

The cheap half, exactly as in the continuous classes: a run is in the set of
what runs reach by construction, so the proof is the pair itself. All the
content sits in the other half, `reachSet_subset_reach`.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Reach for this to say where a run *is*; reach for `reachSet_subset_reach`
to say what encloses it. -/
theorem NeurNetContrSys.Trajectory.reachSet_outer {sys : NeurNetContrSys 𝕋 S n}
    {π : Vec ℝ n → Vec ℝ n} {Δtc : ℝ} {H : ℕ} {R₀ : S n} {x : ℝ → Vec ℝ n}
    (traj : sys.Trajectory π Δtc H R₀ x) (t : ℝ) :
    x t ∈ sys.reachSet π Δtc H R₀ t :=
  ⟨x, traj, rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
