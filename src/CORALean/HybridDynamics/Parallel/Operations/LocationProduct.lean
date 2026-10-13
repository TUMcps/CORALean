module

public import CORALean.HybridDynamics.Parallel.Operations.MergeFlows
public import CORALean.HybridDynamics.Parallel.Operations.MergeInvariants
public import CORALean.HybridDynamics.Parallel.Operations.MergeInputSets
public import CORALean.HybridDynamics.Parallel.Operations.MergeTransitionSets

@[expose] public section

/-!
# `locationProduct`

CORA's `locationProduct`, for the location tuple `ℓ`: the invariant, the transitions and the
flow, merged, as a `Location` of the single automaton. Built on the fly for one tuple, as CORA
does, so no product over all tuples is formed unless `product` asks for it.
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

def ParallelHybridAutomaton.locationProduct [ExactScalar 𝕋]
    (P : ParallelHybridAutomaton S G k L 𝕋 n m)
    (lift : ParallelHybridAutomaton.Lifting S G n m P.binds) (ℓ : ∀ i, L i) :
    Location S G (∀ i, L i) 𝕋 (∑ i, n i) where
  inv := P.mergeInvariants lift ℓ
  dynamics := P.mergeFlows ℓ
  U := P.mergeInputSets lift ℓ
  trans := P.mergeTransitionSets lift ℓ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
