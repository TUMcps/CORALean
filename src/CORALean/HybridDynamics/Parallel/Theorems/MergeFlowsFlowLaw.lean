module

public import CORALean.HybridDynamics.Parallel.Theorems.MergeFlowsMulVec
public import CORALean.HybridDynamics.Parallel.Definitions.FlowLaw

@[expose] public section

/-!
# `mergeFlows` has the flow law, where it is exact

`mergeFlows_mulVec` for every location tuple, in the form `FlowLaw` states.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {𝕋 : Type} [Scalar 𝕋] {k m : ℕ} {n : Fin k → ℕ} {L : Fin k → Type}


-- =======================================  MAIN THEOREM  ======================================= --

omit [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)] in
theorem ParallelHybridAutomaton.mergeFlows_flowLaw [ExactScalar 𝕋]
    {P : ParallelHybridAutomaton S G k L 𝕋 n m} (hself : P.SelfBindFree) :
    P.FlowLaw P.mergeFlows :=
  fun ℓ x i j => P.mergeFlows_mulVec hself ℓ x i j

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
