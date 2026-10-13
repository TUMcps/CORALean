import CORALean.Global.ExactScalar
import CORALean.HybridDynamics.Parallel.Operations.SyncPick
import CORALean.HybridDynamics.Parallel.Definitions.SyncLifting

/-!
# `liftSyncTransition`

CORA's `lift` and `synchronize` of the transitions sharing a label, as one transition of the
product: the guard is the conjunction of the participants' guards (`SyncLifting.guardAll`), the
reset acts on each participant's block by that participant's own reset and is the identity on the
others, and the target moves every participant. A participant with no `λ`-labeled transition at its
location contributes nothing here; `mergeTransitionSetsSync` only keeps this transition when every
participant has one. The product's transition carries no label of its own.
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

def ParallelHybridAutomaton.liftSyncTransition [ExactScalar 𝕋] [DecidableEq Λ]
    (P : ParallelHybridAutomaton S G k L 𝕋 n m)
    {binds : ∀ i, Fin (n i) → InputSource k n m}
    (slift : ParallelHybridAutomaton.SyncLifting S G n m binds)
    (lab : ParallelHybridAutomaton.SyncLabels G L 𝕋 n Λ) (ℓ : ∀ i, L i) (a : Λ) :
    Transition G (∀ i, L i) 𝕋 (∑ i, n i) where
  guard := slift.guardAll fun c => (lab.pick P ℓ a c).map (·.guard)
  W := Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv <| Matrix.of fun p q =>
    match lab.pick P ℓ a p.1 with
    | some e => if h : p.1 = q.1 then e.W p.2 (Fin.cast (congrArg n h.symm) q.2) else 0
    | none => if p = q then 1 else 0
  w := Equiv.piCongrLeft (fun _ => 𝕋) finSigmaFinEquiv fun p =>
    match lab.pick P ℓ a p.1 with
    | some e => e.w p.2
    | none => 0
  target := fun c => match lab.pick P ℓ a c with
    | some e => e.target
    | none => ℓ c

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
