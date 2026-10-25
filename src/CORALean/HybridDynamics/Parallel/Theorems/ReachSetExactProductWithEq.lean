module

public import CORALean.HybridDynamics.Parallel.Theorems.IsRunOfProductWith
public import CORALean.HybridDynamics.Parallel.Theorems.IsRunToProductWith
public import CORALean.HybridDynamics.Parallel.Definitions.ReachSetExact
public import CORALean.HybridDynamics.Definitions.ReachSetExact

@[expose] public section

/-!
# The product reaches exactly the stacks of what the parallel automaton reaches

`IsRun.toProductWith` and `IsRun.ofProductWith` together: the product's exact reachable set, from an
initial set whose stacks are exactly the tuples of the components' initial sets, is the image under
`stack` of the parallel automaton's exact reachable set. An *equality of reachable sets*, under the
conditions of `IsRun.toProductWith` and `IsRun.ofProductWith`; the outer theorems
(`reachFloat_outer`, `reachSetExact_subset_invariant`) enclose either side and are inclusions only.

## Inputs
* `P` – parallel automaton
* `F` – product flow at each location tuple
* `U` – product input sets
* `W` – product disturbance sets
* `lift` – lifting
* `R₀` – initial sets of the components
* `R₀'` – initial set of the product
* `ℓ₀` – initial locations
* `ℓ` – locations reached

## Hypotheses
* `hF` – the flow has the flow law
* `hF'` – the flow has the converse flow law
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

open Matrix ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {𝕋 : Type} [Scalar 𝕋] {k m : ℕ} {n : Fin k → ℕ} {L : Fin k → Type}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `R₀'` is the product's initial set: its stacks are exactly the tuples of `R₀`. -/
theorem ParallelHybridAutomaton.reachSetExact_productWith_eq [ExactScalar 𝕋]
    {P : ParallelHybridAutomaton S G k L 𝕋 n m} {F : (∀ i, L i) → LinearSys 𝕋 (∑ i, n i)}
    {U : ∀ ℓ, S (F ℓ).m} {W : ∀ ℓ, S (F ℓ).r} (hF : P.IsFlowLaw F U W)
    (hF' : P.IsFlowLawConverse F U W) {lift : ParallelHybridAutomaton.Lifting S G n m}
    (hex : lift.IsExact) {R₀ : ∀ i, S (n i)}
    {R₀' : S (∑ i, n i)}
    (hR₀ : ∀ x : ∀ i, Vec ℝ (n i), stack x ∈ construct R₀' ↔ ∀ i, x i ∈ construct (R₀ i))
    (ℓ₀ ℓ : ∀ i, L i) : -- --- CONCL ---
    (P.productWith lift F U W).reachSetExact R₀' ℓ₀ ℓ =
      stack '' P.reachSetExact R₀ ℓ₀ ℓ := by -- --- PROOF ---
  ext w
  constructor
  · rintro ⟨z, hz, run⟩
    refine ⟨unstack w,
      ⟨unstack z, ?_, ParallelHybridAutomaton.IsRun.ofProductWith hF' hex run⟩,
      stack_unstack w⟩
    exact (hR₀ _).mp (by rwa [stack_unstack])
  · rintro ⟨y, ⟨x, hx, run⟩, rfl⟩
    exact ⟨stack x, (hR₀ x).mpr hx, ParallelHybridAutomaton.IsRun.toProductWith hF lift run⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
