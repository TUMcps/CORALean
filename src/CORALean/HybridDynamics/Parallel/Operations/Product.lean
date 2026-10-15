module

public import CORALean.HybridDynamics.Parallel.Operations.LocationProduct
public import CORALean.HybridDynamics.Parallel.Operations.ProductWith

@[expose] public section

/-!
# `product`

The product automaton: one location per tuple of component locations, `locationProduct` at each,
its flow `mergeFlowsLinearSys`. A `HybridAutomaton`, so everything proved of one —
`IsRun.mem_of_invariant`, `reachSet` — applies; `Theorems.IsRunToProduct` says a parallel run is a
run of it. It is `productWith` at `mergeFlowsLinearSys`, `mergeInputSets` and `mergeDistSets`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {k m : ℕ} {n : Fin k → ℕ} {L : Fin k → Type}


-- =====================================  MAIN DEFINITION  ====================================== --

def ParallelHybridAutomaton.product (P : ParallelHybridAutomaton S G k L ℝ n m)
    (lift : ParallelHybridAutomaton.Lifting S G n m) :
    HybridAutomaton S G (∀ i, L i) ℝ (∑ i, n i) where
  loc := P.locationProduct lift

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
