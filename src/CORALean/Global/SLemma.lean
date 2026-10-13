import CORALean.Global.ExistsQuadNeg
import CORALean.Global.SLemmaHomogeneous
import CORALean.Global.Tensor
import Mathlib.Data.Matrix.Mul

/-!
# The S-lemma

Yakubovich's S-lemma for one quadratic constraint: for `f x = xᵀAx + 2aᵀx + α` and
`g x = xᵀBx + 2bᵀx + β` with `g x₀ < 0` for some `x₀` (Slater's condition),
`g x ≤ 0 → f x ≥ 0` holds for every `x` iff `f + δ g ≥ 0` everywhere for some `δ ≥ 0`. It is
the theorem of alternatives the proof of [1, Thm. 13] invokes. Neither `A` nor `B` needs to be
symmetric here: only `xᵀAx` enters.

The proof homogenizes, `P (x, t) = xᵀAx + 2t aᵀx + t²α`, and applies
`s_lemma_homogeneous`. Its hypothesis `Q (x, t) < 0 → P (x, t) ≥ 0` is `g ≤ 0 → f ≥ 0` at
`x / t` for `t ≠ 0`; at `t = 0`, `xᵀBx < 0` and `xᵀAx < 0` would make both `f (s x)` and
`g (s x)` negative for large `s` (`exists_quad_neg`). The certificate read at `t = 1` is
`f + δ g ≥ 0`.

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

/-- The homogenization of `x ↦ xᵀAx + 2aᵀx + α` expands as a quadratic form. -/
theorem aux_hom_expand (A : Mat ℝ n n) (a : Fin n → ℝ) (α u v : ℝ)
    (z w : (Fin n → ℝ) × ℝ) :
    (u • z + v • w).1 ⬝ᵥ A *ᵥ (u • z + v • w).1 + 2 * (u • z + v • w).2 * (a ⬝ᵥ (u • z + v • w).1)
        + (u • z + v • w).2 ^ 2 * α =
      u ^ 2 * (z.1 ⬝ᵥ A *ᵥ z.1 + 2 * z.2 * (a ⬝ᵥ z.1) + z.2 ^ 2 * α)
        + v ^ 2 * (w.1 ⬝ᵥ A *ᵥ w.1 + 2 * w.2 * (a ⬝ᵥ w.1) + w.2 ^ 2 * α)
        + u * v * (z.1 ⬝ᵥ A *ᵥ w.1 + w.1 ⬝ᵥ A *ᵥ z.1 + 2 * z.2 * (a ⬝ᵥ w.1)
          + 2 * w.2 * (a ⬝ᵥ z.1) + 2 * z.2 * w.2 * α) := by
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mulVec_add,
    mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul, smul_dotProduct]
  ring

/-- Off `t = 0` the homogenization is `t² f (x / t)`. -/
theorem aux_hom_eq (A : Mat ℝ n n) (a : Fin n → ℝ) (α : ℝ) (x : Fin n → ℝ) {t : ℝ}
    (ht : t ≠ 0) :
    x ⬝ᵥ A *ᵥ x + 2 * t * (a ⬝ᵥ x) + t ^ 2 * α =
      t ^ 2 * ((t⁻¹ • x) ⬝ᵥ A *ᵥ (t⁻¹ • x) + 2 * (a ⬝ᵥ (t⁻¹ • x)) + α) := by
  simp only [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  field_simp

/-- Along a ray `f (s x)` is a quadratic in `s`. -/
theorem aux_smul_eq (A : Mat ℝ n n) (a : Fin n → ℝ) (α s : ℝ) (x : Fin n → ℝ) :
    (s • x) ⬝ᵥ A *ᵥ (s • x) + 2 * (a ⬝ᵥ (s • x)) + α =
      (x ⬝ᵥ A *ᵥ x) * s ^ 2 + 2 * (a ⬝ᵥ x) * s + α := by
  simp only [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring


-- =======================================  MAIN THEOREM  ======================================= --

/-- The S-lemma: under Slater's condition, `g ≤ 0 → f ≥ 0` iff `f + δ g ≥ 0` for a `δ ≥ 0`. -/
theorem s_lemma (A B : Mat ℝ n n) (a b : Fin n → ℝ) (α β : ℝ)
    (h₀ : ∃ x₀, x₀ ⬝ᵥ B *ᵥ x₀ + 2 * (b ⬝ᵥ x₀) + β < 0) :
    let f := fun x => x ⬝ᵥ A *ᵥ x + 2 * (a ⬝ᵥ x) + α
    let g := fun x => x ⬝ᵥ B *ᵥ x + 2 * (b ⬝ᵥ x) + β
    (∀ x, g x ≤ 0 → 0 ≤ f x) ↔ ∃ δ : ℝ, 0 ≤ δ ∧ ∀ x, 0 ≤ f x + δ * g x := by -- --- PROOF ---
  intro f g
  refine ⟨fun h => ?_, fun ⟨δ, hδ, h⟩ x hx => by nlinarith [h x]⟩
  obtain ⟨x₀, hx₀⟩ := h₀
  -- the homogenized forms satisfy the strict hypothesis of `s_lemma_homogeneous`
  have hPQ : ∀ z : (Fin n → ℝ) × ℝ,
      z.1 ⬝ᵥ B *ᵥ z.1 + 2 * z.2 * (b ⬝ᵥ z.1) + z.2 ^ 2 * β < 0 →
        0 ≤ z.1 ⬝ᵥ A *ᵥ z.1 + 2 * z.2 * (a ⬝ᵥ z.1) + z.2 ^ 2 * α := by
    rintro ⟨x, t⟩ hz
    by_cases ht : t = 0
    · subst ht
      simp only [mul_zero, zero_mul, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow] at hz ⊢
      -- at `t = 0`, both quadratics along the ray `s x` turn negative
      by_contra hA
      push Not at hA
      obtain ⟨s₁, hs₁⟩ := exists_quad_neg hz (2 * (b ⬝ᵥ x)) β
      obtain ⟨s₂, hs₂⟩ := exists_quad_neg hA (2 * (a ⬝ᵥ x)) α
      -- at `s = max s₁ s₂`, `g (s x) ≤ 0` forces `f (s x) ≥ 0`
      have hg := hs₁ (max s₁ s₂) (le_max_left _ _)
      have hf := hs₂ (max s₁ s₂) (le_max_right _ _)
      have := h (max s₁ s₂ • x) (by
        show (max s₁ s₂ • x) ⬝ᵥ B *ᵥ (max s₁ s₂ • x) + 2 * (b ⬝ᵥ (max s₁ s₂ • x)) + β ≤ 0
        rw [aux_smul_eq]; exact hg.le)
      change 0 ≤ (max s₁ s₂ • x) ⬝ᵥ A *ᵥ (max s₁ s₂ • x) + 2 * (a ⬝ᵥ (max s₁ s₂ • x)) + α at this
      rw [aux_smul_eq] at this
      linarith
    · -- off `t = 0` both forms are `t²` times `f`, `g` at `x / t`
      have ht2 : 0 < t ^ 2 := by positivity
      simp only at hz ⊢
      rw [aux_hom_eq B b β x ht] at hz
      rw [aux_hom_eq A a α x ht]
      exact mul_nonneg ht2.le (h _ (nonpos_of_mul_nonpos_right hz.le ht2 |>.trans' le_rfl))
  obtain ⟨δ, hδ, hall⟩ := (s_lemma_homogeneous
    (fun z : (Fin n → ℝ) × ℝ => z.1 ⬝ᵥ A *ᵥ z.1 + 2 * z.2 * (a ⬝ᵥ z.1) + z.2 ^ 2 * α)
    (fun z : (Fin n → ℝ) × ℝ => z.1 ⬝ᵥ B *ᵥ z.1 + 2 * z.2 * (b ⬝ᵥ z.1) + z.2 ^ 2 * β) _ _
    (fun u v z w => aux_hom_expand A a α u v z w) (fun u v z w => aux_hom_expand B b β u v z w)
    ⟨(x₀, 1), by simpa using hx₀⟩).mp hPQ
  -- read at `t = 1`
  refine ⟨δ, hδ, fun x => ?_⟩
  simpa using hall (x, 1)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
