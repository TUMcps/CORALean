module

public import CORALean.HybridDynamics.Parallel.Definitions.Lifting

@[expose] public section

/-!
# `mergeInvariants`

CORA's `mergeInvariants`: the product's invariant is the conjunction of the components', each
lifted, which is `Lifting.inv` of the tuple. CORA also cuts a component's invariant by the
complement of its guards, for the labels it merges; no label is merged here (#40).

## Inputs
* `P` – parallel automaton
* `lift` – lifting
* `ℓ` – current locations

## Output
* invariant of the product
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {𝕋 : Type} [Scalar 𝕋] {k m : ℕ} {n : Fin k → ℕ} {L : Fin k → Type}


-- =====================================  MAIN DEFINITION  ====================================== --

def ParallelHybridAutomaton.mergeInvariants (P : ParallelHybridAutomaton S G k L 𝕋 n m)
    (lift : ParallelHybridAutomaton.Lifting S G n m) (ℓ : ∀ i, L i) : G (∑ i, n i) :=
  lift.inv fun i => ((P.comp i).loc (ℓ i)).inv

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
