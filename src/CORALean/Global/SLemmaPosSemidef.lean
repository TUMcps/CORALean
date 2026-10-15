module

public import CORALean.Global.SLemma
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.PosDef

@[expose] public section

/-!
# The S-lemma as a linear matrix inequality

`s_lemma` with its certificate as a matrix: for symmetric `A`, `B` and Slater's condition,
`g x ≤ 0 → f x ≥ 0` for every `x` iff
`[[A, a], [aᵀ, α]] + δ [[B, b], [bᵀ, β]] ⪰ 0` for some `δ ≥ 0`, the homogenized form in which
[1, Thm. 13] states its constraint (23). The blocks are indexed by `Fin n ⊕ Fin 1`.

A symmetric `[[C, c], [cᵀ, γ]]` is positive semidefinite iff `xᵀCx + 2cᵀx + γ ≥ 0` for every
`x`: at `(x, t)`, `t ≠ 0`, its form is `t²` times that quadratic at `x / t`, and at `t = 0` it
is `xᵀCx`, which a negative value would make the quadratic negative along `s x` for large `s`
(`exists_quad_neg`).

## References

* [1] A. Kulmburg, L. Schäfer and M. Althoff. "Approximability of the Containment Problem for
      Zonotopes and Ellipsotopes". IEEE Transactions on Automatic Control, 2025.
      doi:10.1109/TAC.2025.3583624. arXiv:2404.11185.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The form of `[[C, c], [cᵀ, γ]]` at `(x, y)`. -/
theorem aux_blocks_form (C : Mat ℝ n n) (c : Fin n → ℝ) (γ : ℝ) (x : Fin n → ℝ)
    (y : Fin 1 → ℝ) :
    Sum.elim x y ⬝ᵥ fromBlocks C (replicateCol (Fin 1) c) (replicateRow (Fin 1) c)
        (of fun _ _ => γ) *ᵥ Sum.elim x y =
      x ⬝ᵥ C *ᵥ x + 2 * y 0 * (c ⬝ᵥ x) + y 0 ^ 2 * γ := by -- --- PROOF ---
  rw [fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, sumElim_dotProduct_sumElim]
  simp [mulVec, dotProduct, replicateCol, replicateRow, mul_add, Finset.sum_add_distrib,
    Finset.mul_sum]
  ring_nf
  simp only [show ∀ i, x i * c i * y 0 = y 0 * c i * x i from fun i => by ring,
    ← Finset.sum_mul]
  ring

/-- A symmetric `[[C, c], [cᵀ, γ]]` is positive semidefinite iff `xᵀCx + 2cᵀx + γ ≥ 0`. -/
theorem aux_blocks_posSemidef_iff (C : Mat ℝ n n) (hC : C.IsSymm) (c : Fin n → ℝ) (γ : ℝ) :
    (fromBlocks C (replicateCol (Fin 1) c) (replicateRow (Fin 1) c)
        (of fun _ _ => γ)).PosSemidef ↔
      ∀ x, 0 ≤ x ⬝ᵥ C *ᵥ x + 2 * (c ⬝ᵥ x) + γ := by -- --- PROOF ---
  rw [posSemidef_iff_dotProduct_mulVec]
  simp only [star_trivial]
  refine ⟨fun ⟨_, h⟩ x => ?_, fun h => ⟨?_, fun v => ?_⟩⟩
  · have := h (Sum.elim x fun _ => 1)
    rw [aux_blocks_form] at this
    linarith
  · rw [isHermitian_iff_isSymm]
    refine IsSymm.fromBlocks hC ?_ ?_
    · ext i j; simp [replicateCol, replicateRow]
    · ext i j; simp
  rw [← Sum.elim_comp_inl_inr v, aux_blocks_form]
  set x := v ∘ Sum.inl
  set t := (v ∘ Sum.inr) 0
  by_cases ht : t = 0
  · -- at `t = 0`, a negative `xᵀCx` would make the quadratic negative along `s x`
    rw [ht]
    simp only [mul_zero, zero_mul, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow]
    by_contra hneg
    push Not at hneg
    obtain ⟨s₀, hs₀⟩ := exists_quad_neg hneg (2 * (c ⬝ᵥ x)) γ
    have h1 := h (s₀ • x)
    have h2 := hs₀ s₀ le_rfl
    simp only [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul] at h1
    nlinarith
  · -- off `t = 0`, `t²` times the quadratic at `x / t`
    have := h (t⁻¹ • x)
    simp only [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul] at this
    have heq : x ⬝ᵥ C *ᵥ x + 2 * t * (c ⬝ᵥ x) + t ^ 2 * γ =
        t ^ 2 * (t⁻¹ * (t⁻¹ * (x ⬝ᵥ C *ᵥ x)) + 2 * (t⁻¹ * (c ⬝ᵥ x)) + γ) := by
      field_simp
    rw [heq]
    exact mul_nonneg (sq_nonneg t) this

/-- The certificate's matrix is the block matrix of `f + δ g`. -/
theorem aux_blocks_add (A B : Mat ℝ n n) (a b : Fin n → ℝ) (α β δ : ℝ) :
    fromBlocks A (replicateCol (Fin 1) a) (replicateRow (Fin 1) a) (of fun _ _ => α)
        + δ • fromBlocks B (replicateCol (Fin 1) b) (replicateRow (Fin 1) b) (of fun _ _ => β) =
      fromBlocks (A + δ • B) (replicateCol (Fin 1) (a + δ • b)) (replicateRow (Fin 1) (a + δ • b))
        (of fun _ _ => α + δ * β) := by -- --- PROOF ---
  rw [fromBlocks_smul, fromBlocks_add]
  congr 1


-- =======================================  MAIN THEOREM  ======================================= --

/-- The S-lemma with the certificate `[[A, a], [aᵀ, α]] + δ [[B, b], [bᵀ, β]] ⪰ 0`. -/
theorem s_lemma_posSemidef (A B : Mat ℝ n n) (hA : A.IsSymm) (hB : B.IsSymm) (a b : Fin n → ℝ)
    (α β : ℝ) (h₀ : ∃ x₀, x₀ ⬝ᵥ B *ᵥ x₀ + 2 * (b ⬝ᵥ x₀) + β < 0) :
    (∀ x, x ⬝ᵥ B *ᵥ x + 2 * (b ⬝ᵥ x) + β ≤ 0 → 0 ≤ x ⬝ᵥ A *ᵥ x + 2 * (a ⬝ᵥ x) + α) ↔
      ∃ δ : ℝ, 0 ≤ δ ∧
        (fromBlocks A (replicateCol (Fin 1) a) (replicateRow (Fin 1) a) (of fun _ _ => α)
          + δ • fromBlocks B (replicateCol (Fin 1) b) (replicateRow (Fin 1) b)
            (of fun _ _ => β)).PosSemidef := by -- --- PROOF ---
  have hs := s_lemma A B a b α β h₀
  dsimp only at hs
  rw [hs]
  refine exists_congr fun δ => and_congr_right fun _ => ?_
  rw [aux_blocks_add, aux_blocks_posSemidef_iff _ (hA.add (hB.smul δ))]
  refine forall_congr' fun x => ?_
  -- the quadratic of the sum is `f + δ g`
  have : x ⬝ᵥ (A + δ • B) *ᵥ x + 2 * ((a + δ • b) ⬝ᵥ x) + (α + δ * β) =
      x ⬝ᵥ A *ᵥ x + 2 * (a ⬝ᵥ x) + α + δ * (x ⬝ᵥ B *ᵥ x + 2 * (b ⬝ᵥ x) + β) := by
    simp only [add_mulVec, smul_mulVec, dotProduct_add, add_dotProduct, dotProduct_smul,
      smul_dotProduct, smul_eq_mul]
    ring
  rw [this]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
