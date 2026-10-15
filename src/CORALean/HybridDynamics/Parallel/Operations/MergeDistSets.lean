module

public import CORALean.HybridDynamics.Parallel.Definitions.Lifting

@[expose] public section

/-!
# `mergeDistSets`

The product's disturbance set, CORA's `aux_mergeDistNoiseSet` in `parallelHybridAutomaton/reach`:
the Cartesian product of the components' disturbance sets `W` at the locations `ℓ`, by
`Lifting.dist`, in the stacked disturbance space of `mergeFlowsLinearSys`'s `E`. CORA also forms
the noise sets' product, which no flow reads.
-/

-- Authors:       Claude Opus 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {𝕋 : Type} [Scalar 𝕋] {k m : ℕ} {n : Fin k → ℕ} {L : Fin k → Type}


-- =====================================  MAIN DEFINITION  ====================================== --

def ParallelHybridAutomaton.mergeDistSets (P : ParallelHybridAutomaton S G k L 𝕋 n m)
    (lift : ParallelHybridAutomaton.Lifting S G n m) (ℓ : ∀ i, L i) :
    S (∑ i, (P.sys ℓ i).r) :=
  lift.dist fun i => ((P.comp i).loc (ℓ i)).W

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
