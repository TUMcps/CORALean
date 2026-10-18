module

public import CORALean.HybridDynamics.Parallel.Operations.SyncPick
public import CORALean.HybridDynamics.Operations.TransitionSynchronizeTargetCORA
public import CORALean.HybridDynamics.Parallel.Operations.LiftSyncTransition

@[expose] public section

/-!
# CORA's target of a label-synchronized merged transition

The label-synchronized branch of `@parallelHybridAutomaton/mergeTransitionSets.m` (line 140) hands
the gathered transitions to `transition/synchronize`, whose target loop is
`Transition.synchronizeTargetCORA`. This is that target, locations being numbers as in CORA, one
`let` per printed step. Only the target is modelled; guard and reset are unaffected.

# CORA's `mergeTransitionSets` sends a synchronized jump to the wrong location

Two components share a label; in the current locations their `a`-labeled transitions go to `2`
and `3`. A synchronized jump (`IsSyncRun.sync`, the target of `liftSyncTransition`, which
`IsSyncRun.toProductSync` embeds into `productSync`) lands in `(2, 3)`. The merged transition CORA
builds for the label (`mergeTransitionSets.m:140`, through `synchronize`) targets `(3, 3)`.
Read from the MATLAB code, not run (#40, `references/coverage/hybridDynamics/transition.md`, row
`synchronize`).
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


-- The model: CORA's code as printed, kept only to be refuted.
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

namespace CORALean

open Matrix ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {𝕋 : Type} [Scalar 𝕋] {m : ℕ} {n : Fin 2 → ℕ} {Λ : Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ParallelHybridAutomaton.mergeTransitionSetsCora_wrong_target_counterexample
    [ExactScalar 𝕋] [DecidableEq Λ] (P : ParallelHybridAutomaton S G 2 (fun _ => ℕ) 𝕋 n m)
    (slift : ParallelHybridAutomaton.SyncLifting S G n m)
    (lab : ParallelHybridAutomaton.SyncLabels G (fun _ => ℕ) 𝕋 n Λ) (ℓ : Fin 2 → ℕ) (a : Λ)
    (e₀ : Transition G ℕ 𝕋 (n 0)) (e₁ : Transition G ℕ 𝕋 (n 1))
    (h₀ : lab.pick P ℓ a 0 = some e₀) (h₁ : lab.pick P ℓ a 1 = some e₁)
    (hp₀ : lab.parts a 0 = true) (hp₁ : lab.parts a 1 = true)
    (t₀ : e₀.target = 2) (t₁ : e₁.target = 3) : -- --- STMT ---
    P.mergeTransitionSetsCoraTarget lab ℓ a = ![3, 3] ∧
      (P.liftSyncTransition slift lab ℓ a).target = ![2, 3] ∧
      P.mergeTransitionSetsCoraTarget lab ℓ a ≠
        (P.liftSyncTransition slift lab ℓ a).target := by -- --- PROOF ---
  have hreal : (P.liftSyncTransition slift lab ℓ a).target = ![2, 3] := by
    funext c
    fin_cases c <;> simp [ParallelHybridAutomaton.liftSyncTransition, h₀, h₁, t₀, t₁]
  have hc : (List.finRange 2).filter (fun c => lab.parts a c) = [0, 1] := by
    simp [List.finRange, List.filter, hp₀, hp₁]
  have hcora : P.mergeTransitionSetsCoraTarget lab ℓ a = ![3, 3] := by
    unfold ParallelHybridAutomaton.mergeTransitionSetsCoraTarget
    generalize hl : (List.finRange 2).filter (fun c => lab.parts a c) = l
    obtain rfl : l = [0, 1] := hl.symm.trans hc
    funext c
    fin_cases c <;>
      simp [Transition.synchronizeTargetCORA, List.finRange, h₀, h₁, t₀, t₁, Fin.exists_fin_two]
  refine ⟨hcora, hreal, ?_⟩
  rw [hcora, hreal]
  intro h'
  have := congrFun h' 0
  simp at this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
