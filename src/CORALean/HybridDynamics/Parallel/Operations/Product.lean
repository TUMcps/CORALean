import CORALean.HybridDynamics.Parallel.Operations.LocationProduct

/-!
# `product`

The product automaton: one location per tuple of component locations, `locationProduct` at
each. A `HybridAutomaton`, so everything proved of one — `Run.mem_of_invariant`, `reachSet` —
applies; `Theorems.RunToProduct` says a parallel run is a run of it.
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

def ParallelHybridAutomaton.product [ExactScalar 𝕋] (P : ParallelHybridAutomaton S G k L 𝕋 n m)
    (lift : ParallelHybridAutomaton.Lifting S G n m P.binds) :
    HybridAutomaton S G (∀ i, L i) 𝕋 (∑ i, n i) where
  loc := P.locationProduct lift

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
