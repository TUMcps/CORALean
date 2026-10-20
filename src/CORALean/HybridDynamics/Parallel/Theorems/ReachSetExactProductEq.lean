module

public import CORALean.HybridDynamics.Parallel.Theorems.ReachSetExactProductWithEq
public import CORALean.HybridDynamics.Parallel.Theorems.MergeFlowsLinearSysFlowLaw
public import CORALean.HybridDynamics.Parallel.Theorems.MergeFlowsLinearSysFlowLawConverse
public import CORALean.HybridDynamics.Parallel.Operations.Product

@[expose] public section

/-!
# The product reaches exactly the stacks of what the parallel automaton reaches

`reachSetExact_productWith_eq` at `mergeFlowsLinearSys`, whose flow laws hold at `ℝ` under the
conditions of `IsRun.ofProduct`. An *equality of reachable sets*; the outer theorems
(`reachSetExact_subset_invariant`) enclose either side and are inclusions only.

## Inputs
* `P` – parallel automaton
* `lift` – lifting
* `R₀` – initial sets of the components
* `R₀'` – initial set of the product
* `ℓ₀` – initial locations
* `ℓ` – locations reached

## Hypotheses
* `hfeed` – no feedthrough between bound outputs
* `hdist` – no global input feeds two inputs
* `hne` – every input set is nonempty
* `hex` – lifting is exact
* `hR₀` – product set stacks the component sets

## Conclusion
* the product reaches exactly the stacks of the parallel reach set
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {k m : ℕ} {n : Fin k → ℕ} {L : Fin k → Type}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `R₀'` is the product's initial set: its stacks are exactly the tuples of `R₀`. -/
theorem ParallelHybridAutomaton.reachSetExact_product_eq {P : ParallelHybridAutomaton S G k L ℝ n m}
    (hfeed : P.FeedthroughFree) (hdist : P.GlobalsDistinct)
    (hne : ∀ (ℓ : ∀ i, L i) i, (construct ((P.comp i).loc (ℓ i)).U).Nonempty)
    {lift : ParallelHybridAutomaton.Lifting S G n m} (hex : lift.Exact) {R₀ : ∀ i, S (n i)}
    {R₀' : S (∑ i, n i)}
    (hR₀ : ∀ x : ∀ i, Vec ℝ (n i), stack x ∈ construct R₀' ↔ ∀ i, x i ∈ construct (R₀ i))
    (ℓ₀ ℓ : ∀ i, L i) : -- --- CONCL ---
    (P.product lift).reachSetExact R₀' ℓ₀ ℓ = stack '' P.reachSetExact R₀ ℓ₀ ℓ :=
  ParallelHybridAutomaton.reachSetExact_productWith_eq (P.mergeFlowsLinearSys_flowLaw hfeed lift)
    (P.mergeFlowsLinearSys_flowLawConverse hfeed hdist hne hex) hex hR₀ ℓ₀ ℓ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
