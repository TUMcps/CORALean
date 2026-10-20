module

public import CORALean.HybridDynamics.Theorems.ReachSetExactOuter

@[expose] public section

/-!
# `reachLocationsExact` contains every location a run ends in

`reachSetExact_outer`'s discrete counterpart: the location a run reaches has a
state in `reachSetExact` by construction, namely the one the run ends at, and that
is exactly what `reachLocationsExact` asks for.

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
* the end location is among the reached locations
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

/-- Reach for this to say a location is visited at all; reach for
`reachSetExact_outer` to say by which state. -/
theorem HybridAutomaton.IsRun.reachLocationsExact_outer {HA : HybridAutomaton S G L 𝕋 n} {R₀ : S n}
    {ℓ₀ ℓ : L} {x y : Vec ℝ n} (run : HA.IsRun ℓ₀ x ℓ y) (hx : x ∈ construct R₀) :
    ℓ ∈ HA.reachLocationsExact R₀ ℓ₀ :=
  ⟨y, run.reachSetExact_outer hx⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
