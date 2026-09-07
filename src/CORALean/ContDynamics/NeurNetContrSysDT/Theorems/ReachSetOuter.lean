import CORALean.ContDynamics.NeurNetContrSysDT.ReachSet

/-!
# `reachSet` contains every run

The cheap half, exactly as `LinearSysDT.reachSet_outer`: a run is in the set of
what runs reach by construction, so the proof is the pair itself. All the
content sits in the other half, `reachSet_subset_reach`.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Reach for this to say where a run *is*; reach for `reachSet_subset_reach`
to say what encloses it. -/
theorem NeurNetContrSysDT.Trajectory.reachSet_outer {sys : NeurNetContrSysDT 𝕋 S n}
    {π : Vec ℝ n → Vec ℝ n} {R₀ : S n} {x : ℕ → Vec ℝ n}
    (traj : sys.Trajectory π R₀ x) (k : ℕ) :
    x k ∈ sys.reachSet π R₀ k :=
  ⟨x, traj, rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
