module

public import CORALean.HybridDynamics.Parallel.Operations.MergeTransitionSetsSync
public import CORALean.HybridDynamics.Parallel.Operations.ProductWith

@[expose] public section

/-!
# `productSync`

The product automaton with synchronization labels: `productWith`, with the transitions of
`mergeTransitionSetsSync` in place of `mergeTransitionSets`. Its flow `F`, input sets `U` and
disturbance sets `W` are given, as for `productWith`; `mergeFlowsLinearSys` with `mergeInputSets`
and `mergeDistSets` is CORA's.

## Inputs
* `P` – parallel automaton
* `slift` – lifting with synchronization
* `lab` – synchronization labels
* `F` – product flow at each location tuple
* `U` – product input sets
* `W` – product disturbance sets

## Output
* product automaton with labeled transitions
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {𝕋 : Type} [Scalar 𝕋] {k m : ℕ} {n : Fin k → ℕ} {L : Fin k → Type} {Λ : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

def ParallelHybridAutomaton.productSync [ExactScalar 𝕋] [DecidableEq Λ]
    (P : ParallelHybridAutomaton S G k L 𝕋 n m)
    (slift : ParallelHybridAutomaton.SyncLifting S G n m)
    (lab : ParallelHybridAutomaton.SyncLabels G L 𝕋 n Λ)
    (F : (∀ i, L i) → LinearSys 𝕋 (∑ i, n i)) (U : ∀ ℓ, S (F ℓ).m) (W : ∀ ℓ, S (F ℓ).r) :
    HybridAutomaton S G (∀ i, L i) 𝕋 (∑ i, n i) where
  loc ℓ :=
    { (P.productWith slift.toLifting F U W).loc ℓ with
      trans := P.mergeTransitionSetsSync slift lab ℓ }

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
