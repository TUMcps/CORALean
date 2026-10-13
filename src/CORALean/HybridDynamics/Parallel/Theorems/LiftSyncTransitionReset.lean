import CORALean.HybridDynamics.Parallel.Operations.LiftSyncTransition
import CORALean.HybridDynamics.Parallel.Theorems.StackApply

/-!
# What the synchronized transition's reset does to a stack

`liftTransition_reset` for several components at once: on a stack, the reset is each
participant's own reset on its block and the identity on the others.
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


-- =======================================  MAIN THEOREM  ======================================= --

/-- Each participant resets its block, the others keep theirs. -/
theorem ParallelHybridAutomaton.liftSyncTransition_reset [ExactScalar 𝕋] [DecidableEq Λ]
    (P : ParallelHybridAutomaton S G k L 𝕋 n m)
    (slift : ParallelHybridAutomaton.SyncLifting S G n m P.binds)
    (lab : ParallelHybridAutomaton.SyncLabels G L 𝕋 n Λ) (ℓ : ∀ i, L i) (a : Λ)
    (x : ∀ i, Vec ℝ (n i)) :
    (P.liftSyncTransition slift lab ℓ a).reset (stack x) =
      stack fun c => match lab.pick P ℓ a c with
        | some e => e.reset (x c)
        | none => x c := by -- --- PROOF ---
  classical
  have hs : ∀ (y : ∀ i, Vec ℝ (n i)) (c : Fin k) (s : Fin (n c)),
      stack y (finSigmaFinEquiv ⟨c, s⟩) = y c s := fun y c s => stack_apply y c s
  funext p
  obtain ⟨⟨i, j⟩, rfl⟩ := finSigmaFinEquiv.surjective p
  simp only [Transition.reset, Pi.add_apply, Matrix.mulVec, dotProduct,
    Scalar.toRealMat_apply, Scalar.toRealVec_apply]
  rw [← finSigmaFinEquiv.sum_comp, Fintype.sum_sigma]
  simp only [ParallelHybridAutomaton.liftSyncTransition, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.of_apply,
    Equiv.piCongrLeft_apply_apply, hs]
  cases hp : lab.pick P ℓ a i with
  | none =>
    -- a non-participant: the identity row picks out `x i j` alone
    dsimp only
    simp only [ExactScalar.toReal_zero, add_zero]
    rw [← Fintype.sum_sigma (fun b : Σ i, Fin (n i) =>
      Scalar.toReal (if (⟨i, j⟩ : Σ i, Fin (n i)) = b then (1 : 𝕋) else 0) * x b.1 b.2)]
    rw [Finset.sum_eq_single ⟨i, j⟩]
    · simp [ExactScalar.toReal_one]
    · intro b _ hb
      simp [Ne.symm hb, ExactScalar.toReal_zero]
    · simp
  | some e =>
    -- a participant: the block of its own transition acts
    dsimp only
    rw [Pi.add_apply, Matrix.mulVec, dotProduct, Scalar.toRealVec_apply]
    congr 1
    · rw [Finset.sum_eq_single i]
      · simp [Scalar.toRealMat_apply]
      · intro d _ hd
        refine Finset.sum_eq_zero fun s _ => ?_
        simp [dif_neg (Ne.symm hd), ExactScalar.toReal_zero]
      · simp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
