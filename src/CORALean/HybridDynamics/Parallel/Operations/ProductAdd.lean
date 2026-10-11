import CORALean.HybridDynamics.Parallel.Operations.ProductWith
import CORALean.HybridDynamics.Parallel.Operations.MergeFlowsAdd

/-!
# `productAdd`

The product automaton with `mergeFlowsAdd` for its flow: `product` without `SelfBindFree`, at a
scalar with an exact sum.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {𝕋 : Type} [Scalar 𝕋] {k m : ℕ} {n : Fin k → ℕ} {L : Fin k → Type}


-- =====================================  MAIN DEFINITION  ====================================== --

def ParallelHybridAutomaton.productAdd [ExactScalar 𝕋] [ExactAdd 𝕋]
    (P : ParallelHybridAutomaton S G k L 𝕋 n m)
    (lift : ParallelHybridAutomaton.Lifting S G n m P.binds) :
    HybridAutomaton S G (∀ i, L i) 𝕋 (∑ i, n i) :=
  P.productWith lift P.mergeFlowsAdd

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
