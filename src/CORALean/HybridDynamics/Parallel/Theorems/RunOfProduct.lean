import CORALean.HybridDynamics.Parallel.Theorems.RunOfProductWith
import CORALean.HybridDynamics.Parallel.Theorems.MergeFlowsFlowLaw

/-!
# Every run of the product is a parallel run

`Run.ofProductWith` at `mergeFlows`, whose flow law holds under `SelfBindFree`: the converse of
`Run.toProduct`. The conditions are `Lifting.Exact`, `GlobalsDistinct` and `InputsGlobalOnly`
beside `SelfBindFree`; without the second and third the product has more runs than the parallel
automaton (#40).
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {𝕋 : Type} [Scalar 𝕋] {k m : ℕ} {n : Fin k → ℕ} {L : Fin k → Type}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A run of the product is a run of the parallel automaton, on the blocks of its states. -/
theorem ParallelHybridAutomaton.Run.ofProduct [ExactScalar 𝕋]
    {P : ParallelHybridAutomaton S G k L 𝕋 n m} (hself : P.SelfBindFree)
    (hdist : P.GlobalsDistinct) {lift : ParallelHybridAutomaton.Lifting S G n m P.binds}
    (hex : lift.Exact) (hglob : P.InputsGlobalOnly lift) {ℓ ℓ' : ∀ i, L i}
    {z w : Vec ℝ (∑ i, n i)} (run : (P.product lift).Run ℓ z ℓ' w) :
    P.Run ℓ (unstack z) ℓ' (unstack w) :=
  ParallelHybridAutomaton.Run.ofProductWith (P.mergeFlows_flowLaw hself) hdist hex hglob run

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
