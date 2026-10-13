import CORALean.HybridDynamics.Parallel.Theorems.RunToProductWith
import CORALean.HybridDynamics.Parallel.Theorems.MergeFlowsFlowLaw
import CORALean.HybridDynamics.Parallel.Theorems.LiftTransitionReset

/-!
# Every parallel run is a run of the product

`Run.toProductWith` at `mergeFlows`, whose flow law holds under `SelfBindFree`. The soundness
direction only: the converse is `Run.ofProduct`, under more conditions, since a run of the product
may let the components disagree on a bound input (#40).
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   01-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {𝕋 : Type} [Scalar 𝕋] {k m : ℕ} {n : Fin k → ℕ} {L : Fin k → Type}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A run of the parallel automaton, its states stacked, is a run of its product. -/
theorem ParallelHybridAutomaton.Run.toProduct [ExactScalar 𝕋]
    {P : ParallelHybridAutomaton S G k L 𝕋 n m} (hself : P.SelfBindFree)
    (lift : ParallelHybridAutomaton.Lifting S G n m P.binds) {ℓ ℓ' : ∀ i, L i}
    {x y : ∀ i, Vec ℝ (n i)} (run : P.Run ℓ x ℓ' y) :
    (P.product lift).Run ℓ (stack x) ℓ' (stack y) :=
  ParallelHybridAutomaton.Run.toProductWith (P.mergeFlows_flowLaw hself) lift run

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
