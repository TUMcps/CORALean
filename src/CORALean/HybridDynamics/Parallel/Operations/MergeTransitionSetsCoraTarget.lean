module

public import CORALean.HybridDynamics.Parallel.Operations.SyncPick
public import CORALean.HybridDynamics.Operations.TransitionSynchronizeTargetCORA

@[expose] public section

/-!
# CORA's target of a label-synchronized merged transition

The label-synchronized branch of `@parallelHybridAutomaton/mergeTransitionSets.m` (line 140) hands
the gathered transitions to `transition/synchronize`, whose target loop is
`Transition.synchronizeTargetCORA`. This is that target, locations being numbers as in CORA, one
`let` per printed step. Only the target is modelled; guard and reset are unaffected.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {𝕋 : Type} [Scalar 𝕋] {k m : ℕ} {n : Fin k → ℕ} {Λ : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The target of `transSet(cnt) = synchronize(labelTransSet,idStates,locID,labelCompIdx,...)`. -/
def ParallelHybridAutomaton.mergeTransitionSetsCoraTarget [DecidableEq Λ]
    (P : ParallelHybridAutomaton S G k (fun _ => ℕ) 𝕋 n m)
    (lab : ParallelHybridAutomaton.SyncLabels G (fun _ => ℕ) 𝕋 n Λ)
    (locID : Fin k → ℕ) (syncLabel : Λ) : Fin k → ℕ :=
  -- `[labelTransSet,labelCompIdx] = priv_gatherTransitions(pHA,locID,syncLabel,allLabels)`
  let labelCompIdx := (List.finRange k).filter fun c => lab.parts syncLabel c
  let labelTransSet := fun j : Fin labelCompIdx.length =>
    lab.pick P locID syncLabel (labelCompIdx.get j)
  -- `target(compIdx) = transList(i).target`, in `synchronize`
  Transition.synchronizeTargetCORA locID labelCompIdx.get
    fun j => ((labelTransSet j).map (·.target)).getD (locID (labelCompIdx.get j))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
