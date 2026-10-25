module

public import CORALean.HybridDynamics.HybridAutomaton

@[expose] public section

/-!
# The states and locations a hybrid run actually reaches

The definition is [1, Def. 2], `LinearSys.reachSetExact`'s shape at an `IsRun` instead of an
`IsTrajectory`: `reachSetExact` is every state some run from `ℓ₀` with an initial state in `R₀`
reaches at `ℓ`; `reachLocationsExact` is every `ℓ` it reaches at all. Not indexed by [1, Def. 2]'s
real `r`: no `IsRun` here carries elapsed global time, so both sets are read across every run.
`Theorems.ReachSetExactOuter`/`ReachLocationsExactOuter` put every run into these;
`ReachSetExactSubsetInvariant` puts `reachSetExact` inside what an `IsInvariant` supplies.

## Inputs
* `HA` – hybrid automaton
* `R₀` – initial set
* `ℓ₀` – initial location
* `ℓ` – location reached

## Output
* states some run reaches at the location

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Computing Reachable Sets of Hybrid Systems Using a
      Combination of Zonotopes and Polytopes". Nonlinear Analysis: Hybrid Systems, 2010.
-/

-- Authors:       Claude Sonnet 5
-- Written:       11-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {L 𝕋 : Type} [Scalar 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every state some run of `HA` from `ℓ₀` with an initial state in `R₀`
reaches at `ℓ`: the exact reachable set, and not an enclosure of it. -/
def HybridAutomaton.reachSetExact (HA : HybridAutomaton S G L 𝕋 n) (R₀ : S n) (ℓ₀ ℓ : L) :
    Set (Vec ℝ n) :=
  {y | ∃ x, x ∈ construct R₀ ∧ HA.IsRun ℓ₀ x ℓ y}

/-- Every location some run from `ℓ₀` with an initial state in `R₀` reaches:
The discrete part, as the locations `reachSetExact` is nonempty at. -/
def HybridAutomaton.reachLocationsExact (HA : HybridAutomaton S G L 𝕋 n) (R₀ : S n) (ℓ₀ : L) :
    Set L :=
  {ℓ | (HA.reachSetExact R₀ ℓ₀ ℓ).Nonempty}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
