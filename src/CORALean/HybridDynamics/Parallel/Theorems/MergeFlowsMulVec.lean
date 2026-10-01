import CORALean.HybridDynamics.Parallel.Operations.Product

/-!
# What the merged matrix does to a stack

The merged `A`, read back through `ExactScalar` and applied to the stack of the components'
states, is each component's own `A` on its own state, plus the state a coordinate is bound to.
So the product's flow is the components' flows with the bound inputs filled in: the one
identity `Stay.trajectory` needs, coordinate by coordinate.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {𝕋 : Type} [Scalar 𝕋] {k m : ℕ} {n : Fin k → ℕ} {L : Fin k → Type}


-- =======================================  MAIN THEOREM  ======================================= --

omit [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)] in
/-- Coordinate `⟨i, j⟩` of the merged flow, read on a stack, is component `i`'s own flow plus,
where `binds i j` is a state, that state. -/
theorem ParallelHybridAutomaton.mergeFlows_mulVec [ExactScalar 𝕋]
    (P : ParallelHybridAutomaton S G k L 𝕋 n m) (ℓ : ∀ i, L i) (x : ∀ i, Vec ℝ (n i))
    (i : Fin k) (j : Fin (n i)) :
    (toRealMat (P.mergeFlows ℓ).A *ᵥ stack x) (finSigmaFinEquiv ⟨i, j⟩) =
      (toRealMat ((P.comp i).loc (ℓ i)).dynamics.A *ᵥ x i) j +
      (match P.binds i j with
        | .global _ => 0
        | .state c s => x c s) := by -- --- PROOF ---
  -- read both sides entry by entry, and the sum over the stack as one over the pairs
  classical
  simp only [Matrix.mulVec, dotProduct, ExactScalar.toRealMat_apply]
  rw [← finSigmaFinEquiv.sum_comp, Fintype.sum_sigma]
  -- a coordinate of the stack is the coordinate of its component
  have hs : ∀ (c : Fin k) (s : Fin (n c)), stack x (finSigmaFinEquiv ⟨c, s⟩) = x c s := by
    intro c s; unfold stack; rw [Equiv.symm_apply_apply]
  simp only [ParallelHybridAutomaton.mergeFlows, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Matrix.of_apply, hs,
    ExactScalar.toReal_add, add_mul, Finset.sum_add_distrib]
  -- the block-diagonal part, then the part the binding adds
  congr 1
  · -- only the component `i` of the sum survives
    rw [Finset.sum_eq_single i]
    · simp
    · intro c _ hc
      refine Finset.sum_eq_zero fun s _ => ?_
      simp [dif_neg (Ne.symm hc), ExactScalar.toReal_zero]
    · simp
  · -- a global binding adds nothing; a state binding picks out one coordinate
    cases hb : P.binds i j with
    | global a => simp [ExactScalar.toReal_zero]
    | state c s =>
      rw [← Fintype.sum_sigma (fun b : Σ i, Fin (n i) =>
        ExactScalar.toReal (if (⟨c, s⟩ : Σ i, Fin (n i)) = b then 1 else 0) * x b.1 b.2)]
      rw [Finset.sum_eq_single ⟨c, s⟩]
      · simp [ExactScalar.toReal_one]
      · intro b _ hb
        simp [Ne.symm hb, ExactScalar.toReal_zero]
      · simp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
