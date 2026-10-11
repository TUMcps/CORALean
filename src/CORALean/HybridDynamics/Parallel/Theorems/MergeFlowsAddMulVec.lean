import CORALean.HybridDynamics.Parallel.Operations.MergeFlowsAdd
import CORALean.HybridDynamics.Parallel.Definitions.FlowLaw

/-!
# What the summed matrix does to a stack

`mergeFlows_mulVec` without `SelfBindFree`: the merged matrix, read back and applied to the stack,
is each component's own flow plus the state a coordinate is bound to, the own-component
binding included, since the entry there is the sum `A_js + 1`.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {𝕋 : Type} [Scalar 𝕋] {k m : ℕ} {n : Fin k → ℕ} {L : Fin k → Type}


-- =======================================  MAIN THEOREM  ======================================= --

omit [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)] in
/-- The flow law of `mergeFlowsAdd`, with no hypothesis on the bindings. -/
theorem ParallelHybridAutomaton.mergeFlowsAdd_mulVec [ExactScalar 𝕋] [ExactAdd 𝕋]
    (P : ParallelHybridAutomaton S G k L 𝕋 n m) (ℓ : ∀ i, L i)
    (x : ∀ i, Vec ℝ (n i)) (i : Fin k) (j : Fin (n i)) :
    (toRealMat (P.mergeFlowsAdd ℓ).A *ᵥ stack x) (finSigmaFinEquiv ⟨i, j⟩) =
      (toRealMat ((P.comp i).loc (ℓ i)).dynamics.A *ᵥ x i) j +
      (match P.binds i j with
        | .global _ => 0
        | .state c s => x c s) := by -- --- PROOF ---
  classical
  simp only [Matrix.mulVec, dotProduct, Scalar.toRealMat_apply]
  rw [← finSigmaFinEquiv.sum_comp, Fintype.sum_sigma]
  have hs : ∀ (c : Fin k) (s : Fin (n c)), stack x (finSigmaFinEquiv ⟨c, s⟩) = x c s := by
    intro c s; unfold stack; rw [Equiv.symm_apply_apply]
  -- the block-diagonal sum: only the component `i` of the sum survives
  have hblock : ∑ c, ∑ s, Scalar.toReal (if h : i = c then
      ((P.comp i).loc (ℓ i)).dynamics.A j (Fin.cast (congrArg n h.symm) s) else (0 : 𝕋)) *
        x c s =
      ∑ s, Scalar.toReal (((P.comp i).loc (ℓ i)).dynamics.A j s) * x i s := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro c _ hc
      refine Finset.sum_eq_zero fun s _ => ?_
      simp [dif_neg (Ne.symm hc), ExactScalar.toReal_zero]
    · simp
  simp only [ParallelHybridAutomaton.mergeFlowsAdd, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Matrix.of_apply, hs, ExactAdd.toReal_add, add_mul,
    Finset.sum_add_distrib]
  rw [hblock]
  cases hb : P.binds i j with
  | global a => simp [ExactScalar.toReal_zero]
  | state c₀ s₀ =>
    congr 1
    -- a state binding picks out one coordinate
    simp only [apply_ite Scalar.toReal, ExactScalar.toReal_one, ExactScalar.toReal_zero, ite_mul,
      one_mul, zero_mul]
    rw [Finset.sum_eq_single c₀]
    · simp
    · intro c _ hc
      refine Finset.sum_eq_zero fun s _ => ?_
      have : (⟨c₀, s₀⟩ : Σ i, Fin (n i)) ≠ ⟨c, s⟩ := fun h => hc (Sigma.mk.inj_iff.mp h).1.symm
      simp [this]
    · simp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
