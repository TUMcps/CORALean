import CORALean.HybridDynamics.Parallel.Theorems.RunOfProductWith
import CORALean.HybridDynamics.Parallel.Theorems.RunToProductWith
import CORALean.HybridDynamics.Parallel.Definitions.ReachSet
import CORALean.HybridDynamics.Definitions.ReachSet

/-!
# The product reaches exactly the stacks of what the parallel automaton reaches

`Run.toProductWith` and `Run.ofProductWith` together: the product's exact reachable set, from an
initial set whose stacks are exactly the tuples of the components' initial sets, is the image
under `stack` of the parallel automaton's exact reachable set. An *equality of reachable sets*,
under the conditions of `Run.ofProductWith`; the outer theorems (`reachFloat_outer`,
`reachSet_subset_invariant`) enclose either side and are inclusions only.
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

/-- `R₀'` is the product's initial set: its stacks are exactly the tuples of `R₀`. -/
theorem ParallelHybridAutomaton.reachSet_productWith_eq [ExactScalar 𝕋]
    {P : ParallelHybridAutomaton S G k L 𝕋 n m} {F : (∀ i, L i) → LinearSys 𝕋 (∑ i, n i)}
    (hF : P.FlowLaw F) (hdist : P.GlobalsDistinct)
    {lift : ParallelHybridAutomaton.Lifting S G n m P.binds}
    (hex : lift.Exact) (hglob : P.InputsGlobalOnly lift) {R₀ : ∀ i, S (n i)}
    {R₀' : S (∑ i, n i)}
    (hR₀ : ∀ x : ∀ i, Vec ℝ (n i), stack x ∈ construct R₀' ↔ ∀ i, x i ∈ construct (R₀ i))
    (ℓ₀ ℓ : ∀ i, L i) :
    (P.productWith lift F).reachSet R₀' ℓ₀ ℓ = stack '' P.reachSet R₀ ℓ₀ ℓ := by -- --- PROOF ---
  ext w
  constructor
  · rintro ⟨z, hz, run⟩
    refine ⟨unstack w,
      ⟨unstack z, ?_, ParallelHybridAutomaton.Run.ofProductWith hF hdist hex hglob run⟩,
      stack_unstack w⟩
    exact (hR₀ _).mp (by rwa [stack_unstack])
  · rintro ⟨y, ⟨x, hx, run⟩, rfl⟩
    exact ⟨stack x, (hR₀ x).mpr hx, ParallelHybridAutomaton.Run.toProductWith hF lift run⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
