module

public import CORALean.HybridDynamics.Parallel.Operations.MergeFlowsLinearSys
public import CORALean.HybridDynamics.Parallel.Operations.MergeInvariants
public import CORALean.HybridDynamics.Parallel.Operations.MergeInputSets
public import CORALean.HybridDynamics.Parallel.Operations.MergeDistSets
public import CORALean.HybridDynamics.Parallel.Operations.MergeTransitionSets

@[expose] public section

/-!
# `locationProduct`

CORA's `locationProduct`, for the location tuple `ℓ`: the invariant, the transitions and the flow,
merged, as a `Location` of the single automaton. The flow is `mergeFlowsLinearSys`, CORA's
`mergeFlows` at linear components: the components' whole equations as one, inputs bound to outputs
moved into its `A`, `B` and `c`; its inputs are the global inputs, drawn from `mergeInputSets`, and
its disturbances the stacked ones, from `mergeDistSets`, as CORA's `reach` sets `params.U` and
`params.W` per location tuple. Built on the fly for one tuple, as CORA does, so no product over all
tuples is formed unless `product` asks for it. At `ℝ`, where the merge's sums are exact; at a
float scalar the product is `productWith` at `mergeFlows`.
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

def ParallelHybridAutomaton.locationProduct (P : ParallelHybridAutomaton S G k L ℝ n m)
    (lift : ParallelHybridAutomaton.Lifting S G n m) (ℓ : ∀ i, L i) :
    Location S G (∀ i, L i) ℝ (∑ i, n i) where
  inv := P.mergeInvariants lift ℓ
  dynamics := ParallelHybridAutomaton.mergeFlowsLinearSys (P.sys ℓ) (P.bindsAt ℓ)
  U := P.mergeInputSets lift ℓ
  W := P.mergeDistSets lift ℓ
  trans := P.mergeTransitionSets lift ℓ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
