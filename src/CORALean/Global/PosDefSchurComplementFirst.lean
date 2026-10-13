import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Algebra.Order.Star.Real

/-!
# The strict Schur complement of the first block, both ways

A block matrix `[A  B; Bᵀ  D]` with `A ≻ 0` is positive definite iff `D - Bᵀ A⁻¹ B ≻ 0`. The
direction the linear matrix inequalities of the observer papers use, from `[-Q ⋆; ⋆ ⋆] ≺ 0` to the
quadratic form it stands for and back. Mathlib has the semidefinite equivalence
(`Matrix.PosDef.fromBlocks₁₁`); the strict one is the same quadratic-form identity
(`Matrix.schur_complement_eq₁₁`): the form is a square in `A` plus the form of the complement.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {m k : Type} [Fintype m] [Fintype k] [DecidableEq m]


-- =======================================  MAIN THEOREM  ======================================= --

theorem posDef_fromBlocks_first_iff (A : Matrix m m ℝ) (B : Matrix m k ℝ) (D : Matrix k k ℝ)
    (hA : A.PosDef) :
    (fromBlocks A B Bᵀ D).PosDef ↔ (D - Bᵀ * A⁻¹ * B).PosDef := by -- --- PROOF ---
  haveI : Invertible A := hA.isUnit.invertible
  have hB : Bᴴ = Bᵀ := conjTranspose_eq_transpose_of_trivial B
  have hherm := IsHermitian.fromBlocks₁₁ B D hA.1
  rw [hB] at hherm
  -- the quadratic form of the block matrix: a square in `A`, plus the form of the complement
  have hform : ∀ (x : m → ℝ) (y : k → ℝ),
      (x ⊕ᵥ y) ⬝ᵥ ((fromBlocks A B Bᵀ D) *ᵥ (x ⊕ᵥ y)) =
        (x + (A⁻¹ * B) *ᵥ y) ⬝ᵥ (A *ᵥ (x + (A⁻¹ * B) *ᵥ y)) +
          y ⬝ᵥ ((D - Bᵀ * A⁻¹ * B) *ᵥ y) := by
    intro x y
    have := schur_complement_eq₁₁ B D x y hA.1
    rw [hB] at this
    simpa [dotProduct_mulVec, star_trivial] using this
  rw [posDef_iff_dotProduct_mulVec, posDef_iff_dotProduct_mulVec]
  simp only [star_trivial]
  refine and_congr hherm ⟨fun h y hy => ?_, fun h z hz => ?_⟩
  · -- at `(-A⁻¹ B y, y)` the first term vanishes
    have hw : ((-((A⁻¹ * B) *ᵥ y)) ⊕ᵥ y) ≠ 0 := by
      intro h0
      exact hy (funext fun i => by simpa using congrFun h0 (Sum.inr i))
    have h1 := h hw
    rw [hform] at h1
    simpa using h1
  · -- split `z = (x, y)`
    obtain ⟨x, y, rfl⟩ : ∃ x y, z = x ⊕ᵥ y :=
      ⟨z ∘ Sum.inl, z ∘ Sum.inr, (Sum.elim_comp_inl_inr z).symm⟩
    rw [hform]
    have hA' := (posDef_iff_dotProduct_mulVec.mp hA).2
    by_cases hy : y = 0
    · subst hy
      have hx : x ≠ 0 := fun h0 => hz (by simp [h0])
      simpa using hA' hx
    · have h2 := h hy
      have h1 := (posSemidef_iff_dotProduct_mulVec.mp hA.posSemidef).2 (x + (A⁻¹ * B) *ᵥ y)
      simp only [star_trivial] at h1
      linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
