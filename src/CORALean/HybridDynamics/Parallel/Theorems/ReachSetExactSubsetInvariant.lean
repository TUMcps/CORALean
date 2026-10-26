module

public import CORALean.HybridDynamics.Parallel.Theorems.IsRunMemOfInvariant
public import CORALean.HybridDynamics.Parallel.Definitions.ReachSetExact

@[expose] public section

/-!
# `reachSetExact` of a parallel automaton is inside what the product's invariant supplies

`HybridAutomaton.reachSetExact_subset_isInvariant` for the parallel automaton, stated against
its own `reachSetExact`: every tuple of states reached, stacked, lies in the set the product's
`IsInvariant` gives at that location tuple. This is the outer reachable set of the parallel
automaton, once the product's `IsInvariant` is in hand.

## Inputs
* `P` – parallel automaton
* `lift` – lifting
* `R₀` – initial sets of the components
* `ℓ₀` – initial locations
* `R` – invariant sets of the product
* `ℓ` – locations reached

## Hypotheses
* `hfeed` – no feedthrough between bound outputs
* `hinv` – the sets are an invariant of the product
* `hR₀` – stacked initial states lie in their set

## Conclusion
* stacked reachable states lie in the invariant
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

/-- The stacks of the reachable tuples at `ℓ` lie in the invariant's set at `ℓ`. -/
theorem ParallelHybridAutomaton.reachSetExact_subset_isInvariant
    {P : ParallelHybridAutomaton S G k L ℝ n m} (hfeed : P.IsFeedthroughFree)
    {lift : ParallelHybridAutomaton.Lifting S G n m} {R₀ : ∀ i, S (n i)}
    {ℓ₀ : ∀ i, L i} {R : (∀ i, L i) → S (∑ i, n i)} (hinv : (P.product lift).IsInvariant R)
    (hR₀ : ∀ x : ∀ i, Vec ℝ (n i), (∀ i, x i ∈ construct (R₀ i)) →
      stack x ∈ construct (R ℓ₀)) (ℓ : ∀ i, L i) : -- --- CONCL ---
    stack '' P.reachSetExact R₀ ℓ₀ ℓ ⊆ construct (R ℓ) := by -- --- PROOF ---
  rintro _ ⟨y, ⟨x, hx, run⟩, rfl⟩
  exact run.mem_of_isInvariant hfeed hinv (hR₀ x hx)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
