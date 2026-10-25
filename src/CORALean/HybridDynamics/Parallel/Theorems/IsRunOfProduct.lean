module

public import CORALean.HybridDynamics.Parallel.Theorems.IsRunOfProductWith
public import CORALean.HybridDynamics.Parallel.Theorems.MergeFlowsLinearSysFlowLawConverse
public import CORALean.HybridDynamics.Parallel.Operations.Product

@[expose] public section

/-!
# Every run of the product is a parallel run

`IsRun.ofProductWith` at `mergeFlowsLinearSys`, whose converse flow law holds at `ℝ` under
`IsFeedthroughFree`, `GlobalsDistinct`, an exact `Lifting` and nonempty input sets
(`mergeFlowsLinearSys_flowLawConverse`): the converse of `IsRun.toProduct`. Without
`GlobalsDistinct` or nonempty input sets the product may have more runs than the parallel
automaton (#40).

## Inputs
* `P` – parallel automaton
* `lift` – lifting
* `ℓ` – start locations
* `ℓ'` – end locations
* `z` – start state of the product
* `w` – end state of the product

## Hypotheses
* `hfeed` – no feedthrough between bound outputs
* `hdist` – no global input feeds two inputs
* `hne` – every input set is nonempty
* `hex` – lifting is exact
* `run` – run of the product from `z` to `w`

## Conclusion
* the unstacked states are a parallel run
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   14-October-2026
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {k m : ℕ} {n : Fin k → ℕ} {L : Fin k → Type}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A run of the product is a run of the parallel automaton, on the blocks of its states. -/
theorem ParallelHybridAutomaton.IsRun.ofProduct {P : ParallelHybridAutomaton S G k L ℝ n m}
    (hfeed : P.IsFeedthroughFree) (hdist : P.GlobalsDistinct)
    (hne : ∀ (ℓ : ∀ i, L i) i, (construct ((P.comp i).loc (ℓ i)).U).Nonempty)
    {lift : ParallelHybridAutomaton.Lifting S G n m} (hex : lift.IsExact) {ℓ ℓ' : ∀ i, L i}
    {z w : Vec ℝ (∑ i, n i)} (run : (P.product lift).IsRun ℓ z ℓ' w) :
    P.IsRun ℓ (unstack z) ℓ' (unstack w) :=
  ParallelHybridAutomaton.IsRun.ofProductWith
    (P.mergeFlowsLinearSys_flowLawConverse hfeed hdist hne hex) hex run

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
