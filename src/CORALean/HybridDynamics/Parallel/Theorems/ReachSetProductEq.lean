module

public import CORALean.HybridDynamics.Parallel.Theorems.ReachSetProductWithEq
public import CORALean.HybridDynamics.Parallel.Theorems.MergeFlowsFlowLaw

@[expose] public section

/-!
# The product reaches exactly the stacks of what the parallel automaton reaches

`reachSet_productWith_eq` at `mergeFlows`, whose flow law holds under `SelfBindFree`. An *equality
of reachable sets*, under the conditions of `Run.ofProduct`; the outer theorems
(`reachFloat_outer`, `reachSet_subset_invariant`) enclose either side and are inclusions only.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {𝕋 : Type} [Scalar 𝕋] {k m : ℕ} {n : Fin k → ℕ} {L : Fin k → Type}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `R₀'` is the product's initial set: its stacks are exactly the tuples of `R₀`. -/
theorem ParallelHybridAutomaton.reachSet_product_eq [ExactScalar 𝕋]
    {P : ParallelHybridAutomaton S G k L 𝕋 n m} (hself : P.SelfBindFree)
    (hdist : P.GlobalsDistinct) {lift : ParallelHybridAutomaton.Lifting S G n m P.binds}
    (hex : lift.Exact) (hglob : P.InputsGlobalOnly lift) {R₀ : ∀ i, S (n i)}
    {R₀' : S (∑ i, n i)}
    (hR₀ : ∀ x : ∀ i, Vec ℝ (n i), stack x ∈ construct R₀' ↔ ∀ i, x i ∈ construct (R₀ i))
    (ℓ₀ ℓ : ∀ i, L i) :
    (P.product lift).reachSet R₀' ℓ₀ ℓ = stack '' P.reachSet R₀ ℓ₀ ℓ :=
  ParallelHybridAutomaton.reachSet_productWith_eq (P.mergeFlows_flowLaw hself) hdist hex hglob hR₀
    ℓ₀ ℓ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
