import CORALean.HybridDynamics.Parallel.Operations.MergeFlows
import CORALean.HybridDynamics.Parallel.Operations.MergeInvariants
import CORALean.HybridDynamics.Parallel.Operations.MergeInputSets
import CORALean.HybridDynamics.Parallel.Operations.MergeTransitionSets

/-!
# `locationProduct`

CORA's `locationProduct`, for the location tuple `ℓ`: the invariant, the transitions and the
flow, merged, as a `Location` of the single automaton. Built on the fly for one tuple, as CORA
does, so no product over all tuples is formed unless `product` asks for it.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


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
