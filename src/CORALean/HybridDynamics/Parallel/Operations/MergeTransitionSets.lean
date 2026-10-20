module

public import CORALean.HybridDynamics.Parallel.Operations.LiftTransition

@[expose] public section

/-!
# `mergeTransitionSets`

CORA's `mergeTransitionSets`: every outgoing transition of every component's current location,
lifted. Without synchronization labels each transition is its own product transition, which
is all `Transition` can say. One component jumps at a time; `IsRun` has simultaneous jumps
as consecutive ones.

## Inputs
* `P` – parallel automaton
* `lift` – lifting
* `ℓ` – current locations

## Output
* lifted transitions of all components
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

def ParallelHybridAutomaton.mergeTransitionSets [ExactScalar 𝕋]
    (P : ParallelHybridAutomaton S G k L 𝕋 n m)
    (lift : ParallelHybridAutomaton.Lifting S G n m) (ℓ : ∀ i, L i) :
    List (Transition G (∀ i, L i) 𝕋 (∑ i, n i)) :=
  (List.finRange k).flatMap fun c =>
    ((P.comp c).loc (ℓ c)).trans.map (ParallelHybridAutomaton.liftTransition lift ℓ c)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
