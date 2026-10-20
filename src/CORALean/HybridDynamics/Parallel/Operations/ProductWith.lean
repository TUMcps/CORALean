module

public import CORALean.HybridDynamics.Parallel.Operations.MergeInvariants
public import CORALean.HybridDynamics.Parallel.Operations.MergeTransitionSets

@[expose] public section

/-!
# `productWith`

The product automaton with its flow given: `locationProduct`'s invariant and transitions, and the
flow `F ℓ` with its input set `U ℓ` and disturbance set `W ℓ` in place of `mergeFlowsLinearSys`,
`mergeInputSets` and `mergeDistSets`. `product` is the instance at those three; the run theorems
are proved for any flow with `FlowLaw`, so that a flow assembled at a float scalar, where
`mergeFlowsLinearSys`'s sums would round, is covered by the same proof.

## Inputs
* `P` – parallel automaton
* `lift` – lifting
* `F` – product flow at each location tuple
* `U` – product input sets
* `W` – product disturbance sets

## Output
* product automaton with the given flow
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {𝕋 : Type} [Scalar 𝕋] {k m : ℕ} {n : Fin k → ℕ} {L : Fin k → Type}


-- =====================================  MAIN DEFINITION  ====================================== --

def ParallelHybridAutomaton.productWith [ExactScalar 𝕋]
    (P : ParallelHybridAutomaton S G k L 𝕋 n m)
    (lift : ParallelHybridAutomaton.Lifting S G n m)
    (F : (∀ i, L i) → LinearSys 𝕋 (∑ i, n i)) (U : ∀ ℓ, S (F ℓ).m) (W : ∀ ℓ, S (F ℓ).r) :
    HybridAutomaton S G (∀ i, L i) 𝕋 (∑ i, n i) where
  loc ℓ :=
    { inv := P.mergeInvariants lift ℓ
      dynamics := F ℓ
      U := U ℓ
      W := W ℓ
      trans := P.mergeTransitionSets lift ℓ }

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
