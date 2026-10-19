module

public import CORALean.HybridDynamics.Parallel.Operations.Product

@[expose] public section

/-!
# A lifted reset moves one component

`liftTransition` puts a component's reset on its block of the stack and the identity everywhere
else, so the product's reset of a stack is the stack of the states with that one component's
replaced. That is the update `ParallelHybridAutomaton.IsRun.jump` writes, and it is what lets
`IsRun.toProduct` take the product's jump to the parallel one.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   01-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {𝕋 : Type} [Scalar 𝕋] {k m : ℕ} {n : Fin k → ℕ} {L : Fin k → Type}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The product's reset on a stack is the component's reset on its block and the identity
elsewhere. -/
theorem ParallelHybridAutomaton.liftTransition_reset [ExactScalar 𝕋]
    (lift : ParallelHybridAutomaton.Lifting S G n m) (ℓ : ∀ i, L i) (c : Fin k)
    (e : Transition G (L c) 𝕋 (n c)) (x : ∀ i, Vec ℝ (n i)) : -- --- CONCL ---
    (ParallelHybridAutomaton.liftTransition lift ℓ c e).reset (stack x) =
      stack (Function.update x c (e.reset (x c))) := by -- --- PROOF ---
  -- compare coordinate `⟨i, j⟩` of both sides, reading the sums over the pairs
  classical
  have hs : ∀ (y : ∀ i, Vec ℝ (n i)) (c : Fin k) (s : Fin (n c)),
      stack y (finSigmaFinEquiv ⟨c, s⟩) = y c s := by
    intro y c s; unfold stack; rw [Equiv.symm_apply_apply]
  -- a coordinate of the stack is the coordinate of its component
  funext p
  obtain ⟨⟨i, j⟩, rfl⟩ := finSigmaFinEquiv.surjective p
  simp only [Transition.reset, Pi.add_apply, Matrix.mulVec, dotProduct,
    Scalar.toRealMat_apply, Scalar.toRealVec_apply]
  rw [← finSigmaFinEquiv.sum_comp, Fintype.sum_sigma]
  simp only [ParallelHybridAutomaton.liftTransition, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Matrix.of_apply, Equiv.piCongrLeft_apply_apply, hs]
  -- in the reset component the block of `e` acts; elsewhere the identity does
  by_cases h : i = c
  · subst h
    rw [Function.update_self, Pi.add_apply, Matrix.mulVec, dotProduct,
      Scalar.toRealVec_apply]
    congr 1
    · rw [Finset.sum_eq_single i]
      · simp [Scalar.toRealMat_apply]
      · intro d _ hd
        refine Finset.sum_eq_zero fun s _ => ?_
        simp [hd, ExactScalar.toReal_zero]
      · simp
    · simp
  · -- off the block: the identity row picks out `x i j` alone
    rw [Function.update_of_ne h]
    simp only [dif_neg h, ExactScalar.toReal_zero, add_zero]
    rw [← Fintype.sum_sigma (fun b : Σ i, Fin (n i) =>
      Scalar.toReal (if (⟨i, j⟩ : Σ i, Fin (n i)) = b then 1 else 0) * x b.1 b.2)]
    rw [Finset.sum_eq_single ⟨i, j⟩]
    · simp [ExactScalar.toReal_one]
    · intro b _ hb
      simp [Ne.symm hb, ExactScalar.toReal_zero]
    · simp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
