module

public import CORALean.HybridDynamics.Parallel.Theorems.IsRunToProductWith
public import CORALean.HybridDynamics.Parallel.Theorems.MergeFlowsLinearSysFlowLaw
public import CORALean.HybridDynamics.Parallel.Operations.Product
public import CORALean.HybridDynamics.Parallel.Theorems.LiftTransitionReset

@[expose] public section

/-!
# Every parallel run is a run of the product

`IsRun.toProductWith` at `mergeFlowsLinearSys`, whose flow law holds at `ℝ` under
`IsFeedthroughFree`, CORA's own check against algebraic loops. The soundness direction; the converse
is `IsRun.ofProduct`, under more conditions.

## Inputs
* `P` – parallel automaton
* `lift` – lifting
* `ℓ` – start locations
* `ℓ'` – end locations
* `x` – start states
* `y` – end states

## Hypotheses
* `hfeed` – no feedthrough between bound outputs
* `run` – parallel run from `x` to `y`

## Conclusion
* the stacked states are a run of the product
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


-- =======================================  MAIN THEOREM  ======================================= --

/-- A run of the parallel automaton, its states stacked, is a run of its product. -/
theorem ParallelHybridAutomaton.IsRun.toProduct {P : ParallelHybridAutomaton S G k L ℝ n m}
    (hfeed : P.IsFeedthroughFree) (lift : ParallelHybridAutomaton.Lifting S G n m)
    {ℓ ℓ' : ∀ i, L i} {x y : ∀ i, Vec ℝ (n i)} (run : P.IsRun ℓ x ℓ' y) :
    (P.product lift).IsRun ℓ (stack x) ℓ' (stack y) :=
  ParallelHybridAutomaton.IsRun.toProductWith (P.mergeFlowsLinearSys_flowLaw hfeed lift) lift run

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
