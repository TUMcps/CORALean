module

public import CORALean.ContDynamics.NeurNetContrSysDT.Definitions.ReachSet

@[expose] public section

/-!
# `reachSet` contains every run

The cheap half, exactly as `LinearSysDT.reachSet_outer`: a run is in the set of
what runs reach by construction, so the proof is the pair itself. All the
content sits in the other half, `reachSet_subset_reach`.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       07-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet ContDynamicsDT

variable {n : ℕ} {P : Type} [ContDynamicsDT P n]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Reach for this to say where a run *is*; reach for `reachSet_subset_reach`
to say what encloses it. -/
theorem NeurNetContrSysDT.IsTrajectory.reachSet_outer {sys : NeurNetContrSysDT P S n}
    {π : Vec ℝ n → Vec ℝ sys.m} {R₀ : S n} {U_ext : Set (Vec ℝ sys.nExt)}
    {W : Set (Vec ℝ (nrOfDisturbances sys.plant))} {x : ℕ → Vec ℝ n} {v : ℕ → Vec ℝ sys.nExt}
    {w : ℕ → Vec ℝ (nrOfDisturbances sys.plant)} (traj : sys.IsTrajectory π R₀ U_ext W x v w)
    (k : ℕ) : x k ∈ sys.reachSet π R₀ U_ext W k :=
  ⟨x, v, w, traj, rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
