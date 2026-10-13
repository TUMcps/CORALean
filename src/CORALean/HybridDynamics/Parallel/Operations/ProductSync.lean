module

public import CORALean.HybridDynamics.Parallel.Operations.MergeTransitionSetsSync
public import CORALean.HybridDynamics.Parallel.Operations.ProductWith

@[expose] public section

/-!
# `productSync`

The product automaton with synchronization labels: `productWith`, with the transitions of
`mergeTransitionSetsSync` in place of `mergeTransitionSets`. Its flow `F` is given, as for
`productWith`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {𝕋 : Type} [Scalar 𝕋] {k m : ℕ} {n : Fin k → ℕ} {L : Fin k → Type} {Λ : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

def ParallelHybridAutomaton.productSync [ExactScalar 𝕋] [DecidableEq Λ]
    (P : ParallelHybridAutomaton S G k L 𝕋 n m)
    (slift : ParallelHybridAutomaton.SyncLifting S G n m P.binds)
    (lab : ParallelHybridAutomaton.SyncLabels G L 𝕋 n Λ)
    (F : (∀ i, L i) → LinearSys 𝕋 (∑ i, n i)) :
    HybridAutomaton S G (∀ i, L i) 𝕋 (∑ i, n i) where
  loc ℓ :=
    { P.locationProduct slift.toLifting ℓ with
      dynamics := F ℓ
      trans := P.mergeTransitionSetsSync slift lab ℓ }

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
