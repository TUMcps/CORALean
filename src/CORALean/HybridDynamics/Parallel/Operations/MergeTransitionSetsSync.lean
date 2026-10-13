module

public import CORALean.HybridDynamics.Parallel.Operations.LiftSyncTransition
public import CORALean.HybridDynamics.Parallel.Operations.MergeTransitionSets

@[expose] public section

/-!
# `mergeTransitionSetsSync`

CORA's `mergeTransitionSets` with synchronization labels: every unlabeled transition of every
component's current location, lifted alone as before, followed by one synchronized transition
for each label `λ` whose participants all have a `λ`-labeled transition here
(`priv_gatherTransitions` returns empty otherwise). A labeled transition is not lifted alone:
this is what `mergeTransitionSets` cannot say.

CORA also cuts a component's invariant by the complement of the guards of the merged labels
(`mergeInvariants`); that cut is not made here, so the product's invariant is the larger,
uncut one. See `FINDINGS.md` for what the cut does in CORA's code.
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

def ParallelHybridAutomaton.mergeTransitionSetsSync [ExactScalar 𝕋] [DecidableEq Λ]
    (P : ParallelHybridAutomaton S G k L 𝕋 n m)
    (slift : ParallelHybridAutomaton.SyncLifting S G n m P.binds)
    (lab : ParallelHybridAutomaton.SyncLabels G L 𝕋 n Λ) (ℓ : ∀ i, L i) :
    List (Transition G (∀ i, L i) 𝕋 (∑ i, n i)) :=
  let unlabeled := (List.finRange k).flatMap fun c =>
    (((P.comp c).loc (ℓ c)).trans.filter fun e => (lab.label c e).isNone).map
      (ParallelHybridAutomaton.liftTransition slift.toLifting ℓ c)
  let synchronized := lab.labels.filterMap fun a =>
    if ∀ c, lab.parts a c = true → (lab.pick P ℓ a c).isSome then
      some (P.liftSyncTransition slift lab ℓ a)
    else none
  unlabeled ++ synchronized

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
