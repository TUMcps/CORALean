import CORALean.HybridDynamics.Parallel.Definitions.SelfBindFree
import CORALean.HybridDynamics.Parallel.Operations.Product

/-!
# What the merged matrix does to a stack

The merged `A`, read back through `ExactScalar` and applied to the stack of the components'
states, is each component's own `A` on its own state, plus the state a coordinate is bound to.
So the product's flow is the components' flows with the bound inputs filled in: the one
identity `Stay.trajectory` needs, coordinate by coordinate.
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

omit [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)] in
/-- Coordinate `⟨i, j⟩` of the merged flow, read on a stack, is component `i`'s own flow plus,
where `binds i j` is a state, that state. -/
theorem ParallelHybridAutomaton.mergeFlows_mulVec [ExactScalar 𝕋]
    (P : ParallelHybridAutomaton S G k L 𝕋 n m) (hself : P.SelfBindFree) (ℓ : ∀ i, L i)
    (x : ∀ i, Vec ℝ (n i)) (i : Fin k) (j : Fin (n i)) :
    (toRealMat (P.mergeFlows ℓ).A *ᵥ stack x) (finSigmaFinEquiv ⟨i, j⟩) =
      (toRealMat ((P.comp i).loc (ℓ i)).dynamics.A *ᵥ x i) j +
      (match P.binds i j with
        | .global _ => 0
        | .state c s => x c s) := by -- --- PROOF ---
  -- read both sides entry by entry, and the sum over the stack as one over the pairs
  classical
  simp only [Matrix.mulVec, dotProduct, Scalar.toRealMat_apply]
  rw [← finSigmaFinEquiv.sum_comp, Fintype.sum_sigma]
  -- a coordinate of the stack is the coordinate of its component
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
  simp only [ParallelHybridAutomaton.mergeFlows, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Matrix.of_apply, hs]
  cases hb : P.binds i j with
  | global a =>
    rw [add_zero]
    exact hblock
  | state c₀ s₀ =>
    -- each entry is the block's, plus a `1` at the bound state
    have hent : ∀ (c : Fin k) (s : Fin (n c)),
        Scalar.toReal (if (⟨c₀, s₀⟩ : Σ i, Fin (n i)) = ⟨c, s⟩ then (1 : 𝕋) else if h : i = c then
          ((P.comp i).loc (ℓ i)).dynamics.A j (Fin.cast (congrArg n h.symm) s) else 0) =
        Scalar.toReal (if h : i = c then
          ((P.comp i).loc (ℓ i)).dynamics.A j (Fin.cast (congrArg n h.symm) s) else (0 : 𝕋)) +
        (if (⟨c₀, s₀⟩ : Σ i, Fin (n i)) = ⟨c, s⟩ then 1 else 0) := by
      intro c s
      -- at the bound state the entry is `1`, and the block's own entry there is `0`
      by_cases he : (⟨c₀, s₀⟩ : Σ i, Fin (n i)) = ⟨c, s⟩
      · rw [if_pos he, if_pos he, ExactScalar.toReal_one]
        obtain ⟨rfl, hh⟩ := Sigma.mk.inj_iff.mp he
        have hh' : s₀ = s := eq_of_heq hh
        subst hh'
        by_cases hi : i = c₀
        · subst hi
          have := hself ℓ i j s₀ hb
          rw [Scalar.toRealMat_apply] at this
          simp [this]
        · simp [hi, ExactScalar.toReal_zero]
      · rw [if_neg he, if_neg he, add_zero]
    simp only [hent, add_mul, Finset.sum_add_distrib]
    rw [hblock]
    congr 1
    -- a state binding picks out one coordinate
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_eq_single c₀]
    · simp
    · intro c _ hc
      refine Finset.sum_eq_zero fun s _ => ?_
      have : (⟨c₀, s₀⟩ : Σ i, Fin (n i)) ≠ ⟨c, s⟩ := fun h => hc (Sigma.mk.inj_iff.mp h).1.symm
      simp [this]
    · simp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
