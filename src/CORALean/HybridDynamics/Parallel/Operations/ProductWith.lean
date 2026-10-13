import CORALean.HybridDynamics.Parallel.Operations.LocationProduct

/-!
# `productWith`

The product automaton with its flow given: `locationProduct`'s invariant, input set and
transitions, and the flow `F ℓ` in place of `mergeFlows`. `product` is `productWith mergeFlows`;
the run theorems are proved for any `F` with `FlowLaw`, so that `mergeFlowsAdd` (which has no
`SelfBindFree`) is covered by the same proof.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {𝕋 : Type} [Scalar 𝕋] {k m : ℕ} {n : Fin k → ℕ} {L : Fin k → Type}


-- =====================================  MAIN DEFINITION  ====================================== --

def ParallelHybridAutomaton.productWith [ExactScalar 𝕋]
    (P : ParallelHybridAutomaton S G k L 𝕋 n m)
    (lift : ParallelHybridAutomaton.Lifting S G n m P.binds)
    (F : (∀ i, L i) → LinearSys 𝕋 (∑ i, n i)) :
    HybridAutomaton S G (∀ i, L i) 𝕋 (∑ i, n i) where
  loc ℓ := { P.locationProduct lift ℓ with dynamics := F ℓ }

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
