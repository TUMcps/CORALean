module

public import CORALean.HybridDynamics.Definitions.ReachSetExact

@[expose] public section

/-!
# `reachSetExact` contains every run

The cheap half, as `LinearSys.IsCanonicalTrajectory.reachSetExact_outer` is: a run is in the
set of what runs reach by construction, so the proof is the pair itself.

## Inputs
* `HA` – hybrid automaton
* `R₀` – initial set
* `ℓ₀` – initial location
* `ℓ` – end location
* `x` – start state
* `y` – end state

## Hypotheses
* `run` – run of the automaton from `x` to `y`
* `hx` – start state lies in the initial set

## Conclusion
* the end state lies in the reachable set
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

/-- Reach for this to say where a run *is*; reach for `reachSetExact_subset_invariant`
to say what encloses it. -/
theorem HybridAutomaton.IsRun.reachSetExact_outer {HA : HybridAutomaton S G L 𝕋 n} {R₀ : S n}
    {ℓ₀ ℓ : L} {x y : Vec ℝ n} (run : HA.IsRun ℓ₀ x ℓ y) (hx : x ∈ construct R₀) :
    y ∈ HA.reachSetExact R₀ ℓ₀ ℓ :=
  ⟨x, hx, run⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
