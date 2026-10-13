import CORALean.HybridDynamics.Parallel.Definitions.Lifting

/-!
# `mergeInputSets`

The product's input set: the components' `U` put together by `Lifting.input`. CORA has no such
function, its input set being the caller's `params.U`; here each location carries one, so
the product's is built from them.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {𝕋 : Type} [Scalar 𝕋] {k m : ℕ} {n : Fin k → ℕ} {L : Fin k → Type}


-- =====================================  MAIN DEFINITION  ====================================== --

def ParallelHybridAutomaton.mergeInputSets (P : ParallelHybridAutomaton S G k L 𝕋 n m)
    (lift : ParallelHybridAutomaton.Lifting S G n m P.binds) (ℓ : ∀ i, L i) : S (∑ i, n i) :=
  lift.input fun i => ((P.comp i).loc (ℓ i)).U

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
