module

public import CORALean.HybridDynamics.Parallel.Operations.MergeInputSets

@[expose] public section

/-!
# The product's inputs vanish where a state is bound

A state-bound coordinate enters the product through the matrix, and `globalInput` zeroes it in the
input. The product's input set, the lifted `U`s, may nevertheless contain a vector that is
nonzero there (a component's `U` need only contain `0` at such a coordinate, as a box
`[-1, 1]` does), and such an input adds to the state-bound input a term that no parallel run has.
`InputsGlobalOnly` says the product's input set has none: each of its vectors is the stack of a
`globalInput`. It is a property of the set, hence of the components' `U` and the `Lifting`, and
the converse of `Run.toProduct` assumes it.
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


-- =====================================  MAIN DEFINITION  ====================================== --

def ParallelHybridAutomaton.InputsGlobalOnly (P : ParallelHybridAutomaton S G k L 𝕋 n m)
    (lift : ParallelHybridAutomaton.Lifting S G n m P.binds) : Prop :=
  ∀ (ℓ : ∀ i, L i) (w : Vec ℝ (∑ i, n i)), w ∈ construct (P.mergeInputSets lift ℓ) →
    ∃ v : ∀ i, Vec ℝ (n i), w = stack (globalInput P.binds v)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
