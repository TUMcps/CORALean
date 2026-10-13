module

public import CORALean.HybridDynamics.Parallel.Theorems.MergeFlowsAddMulVec

@[expose] public section

/-!
# `mergeFlowsAdd` has the flow law

`mergeFlowsAdd_mulVec` for every location tuple, in the form `FlowLaw` states, with no
`SelfBindFree`: the hypothesis `mergeFlows_flowLaw` needs.
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


-- =======================================  MAIN THEOREM  ======================================= --

omit [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)] in
/-- `mergeFlowsAdd` has the flow law. -/
theorem ParallelHybridAutomaton.mergeFlowsAdd_flowLaw [ExactScalar 𝕋] [ExactAdd 𝕋]
    (P : ParallelHybridAutomaton S G k L 𝕋 n m) : P.FlowLaw P.mergeFlowsAdd :=
  fun ℓ x i j => P.mergeFlowsAdd_mulVec ℓ x i j

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
