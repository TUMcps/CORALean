module

public import CORALean.HybridDynamics.Parallel.ParallelHybridAutomaton

@[expose] public section

/-!
# The states a parallel run actually reaches

`HybridAutomaton.reachSet` at a `ParallelHybridAutomaton.Run`: every tuple of component states
some run from `ℓ₀`, with each component's initial state in that component's `R₀ i`, reaches at
`ℓ`. The exact set, not an enclosure; `Theorems.ReachSetSubsetInvariant` bounds it.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {𝕋 : Type} [Scalar 𝕋] {k m : ℕ} {n : Fin k → ℕ} {L : Fin k → Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every tuple of component states some run from `ℓ₀` with initial states in `R₀` reaches
at `ℓ`: the exact reachable set. -/
def ParallelHybridAutomaton.reachSet (P : ParallelHybridAutomaton S G k L 𝕋 n m)
    (R₀ : ∀ i, S (n i)) (ℓ₀ ℓ : ∀ i, L i) : Set (∀ i, Vec ℝ (n i)) :=
  {y | ∃ x, (∀ i, x i ∈ construct (R₀ i)) ∧ P.Run ℓ₀ x ℓ y}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
