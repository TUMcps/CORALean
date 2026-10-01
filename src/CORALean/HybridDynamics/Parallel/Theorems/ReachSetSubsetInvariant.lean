import CORALean.HybridDynamics.Parallel.Theorems.RunMemOfInvariant
import CORALean.HybridDynamics.Parallel.Definitions.ReachSet

/-!
# `reachSet` of a parallel automaton is inside what the product's invariant supplies

`HybridAutomaton.reachSet_subset_invariant` for the parallel automaton, stated against its own
`reachSet`: every tuple of states reached, stacked, lies in the set the product's `Invariant`
gives at that location tuple. This is the outer reachable set of the parallel automaton, once
the product's `Invariant` is in hand.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {𝕋 : Type} [Scalar 𝕋] {k m : ℕ} {n : Fin k → ℕ} {L : Fin k → Type}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The stacks of the reachable tuples at `ℓ` lie in the invariant's set at `ℓ`. -/
theorem ParallelHybridAutomaton.reachSet_subset_invariant [ExactScalar 𝕋]
    {P : ParallelHybridAutomaton S G k L 𝕋 n m}
    {lift : ParallelHybridAutomaton.Lifting S G n m P.binds} {R₀ : ∀ i, S (n i)}
    {ℓ₀ : ∀ i, L i} {R : (∀ i, L i) → S (∑ i, n i)} (hinv : (P.product lift).Invariant R)
    (hR₀ : ∀ x : ∀ i, Vec ℝ (n i), (∀ i, x i ∈ construct (R₀ i)) →
      stack x ∈ construct (R ℓ₀)) (ℓ : ∀ i, L i) :
    stack '' P.reachSet R₀ ℓ₀ ℓ ⊆ construct (R ℓ) := by
  rintro _ ⟨y, ⟨x, hx, run⟩, rfl⟩
  exact run.mem_of_invariant hinv (hR₀ x hx)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
