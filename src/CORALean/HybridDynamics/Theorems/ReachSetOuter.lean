module

public import CORALean.HybridDynamics.Definitions.ReachSet

@[expose] public section

/-!
# `reachSet` contains every run

The cheap half, as `LinearSys.IsCanonicalTrajectory.reachSet_outer` is: a run is in the
set of what runs reach by construction, so the proof is the pair itself.
-/

-- Authors:       Claude Opus 5
-- Written:       11-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {L 𝕋 : Type} [Scalar 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Reach for this to say where a run *is*; reach for `reachSet_subset_invariant`
to say what encloses it. -/
theorem HybridAutomaton.IsRun.reachSet_outer {HA : HybridAutomaton S G L 𝕋 n} {R₀ : S n}
    {ℓ₀ ℓ : L} {x y : Vec ℝ n} (run : HA.IsRun ℓ₀ x ℓ y) (hx : x ∈ construct R₀) :
    y ∈ HA.reachSet R₀ ℓ₀ ℓ :=
  ⟨x, hx, run⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
