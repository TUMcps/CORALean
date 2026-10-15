module

public import CORALean.HybridDynamics.Parallel.Definitions.Lifting

@[expose] public section

/-!
# `mergeInputSets`

The product's input set, CORA's `aux_mergeInputSet` in `parallelHybridAutomaton/reach`: a set of
global-input vectors, built by `Lifting.input` from the components' input sets `U` at the
bindings of the locations `ℓ`. CORA assembles it from the caller's `params.Uloc`; here each
location carries its own `U`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {𝕋 : Type} [Scalar 𝕋] {k m : ℕ} {n : Fin k → ℕ} {L : Fin k → Type}


-- =====================================  MAIN DEFINITION  ====================================== --

def ParallelHybridAutomaton.mergeInputSets (P : ParallelHybridAutomaton S G k L 𝕋 n m)
    (lift : ParallelHybridAutomaton.Lifting S G n m) (ℓ : ∀ i, L i) : S m :=
  lift.input (P.bindsAt ℓ) fun i => ((P.comp i).loc (ℓ i)).U

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
