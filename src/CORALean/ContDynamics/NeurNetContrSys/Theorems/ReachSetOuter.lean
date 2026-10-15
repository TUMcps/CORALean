module

public import CORALean.ContDynamics.NeurNetContrSys.Definitions.ReachSet

@[expose] public section

/-!
# `reachSet` contains every sampled run

The cheap half, exactly as in the continuous classes: a run is in the set of
what runs reach by construction, so the proof is the pair itself. All the
content sits in the other half, `reachSet_subset_reach`.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       07-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet
open ContDynamics

variable {n : ℕ} {P : Type} [ContDynamics P n]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Reach for this to say where a run *is*; reach for `reachSet_subset_reach`
to say what encloses it. -/
theorem NeurNetContrSys.Trajectory.reachSet_outer {sys : NeurNetContrSys P S n}
    {π : Vec ℝ n → Vec ℝ (nrOfInputs sys.plant)} {Δtc : ℝ} {H : ℕ} {R₀ : S n}
    {W : Set (Vec ℝ (nrOfDisturbances sys.plant))} {x : ℝ → Vec ℝ n}
    {w : ℝ → Vec ℝ (nrOfDisturbances sys.plant)}
    (traj : sys.Trajectory π Δtc H R₀ W x w) (t : ℝ) :
    x t ∈ sys.reachSet π Δtc H R₀ W t :=
  ⟨x, w, traj, rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
