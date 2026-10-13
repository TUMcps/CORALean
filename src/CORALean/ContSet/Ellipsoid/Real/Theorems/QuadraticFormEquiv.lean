module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Matrix.Order

@[expose] public section

/-!
# An ellipsoid in shape-matrix form and in quadratic form

[1, Eq. 5] and [1, Eq. 6]: for positive-definite `Q`, `(x − q)ᵀ Q⁻¹ (x − q) ≤ 1` is
`xᵀ A x + 2 xᵀ b + c ≤ 0` with `A = Q⁻¹`, `b = −Q⁻¹ q`, `c = qᵀ Q⁻¹ q − 1`; and back,
`Q = A⁻¹` and `q = −Q b`. Expanding the left side, the cross terms agree because `Q⁻¹` is
symmetric.

## References

* [1] A. Halder. "On the parameterized computation of minimum volume outer ellipsoid of
      Minkowski sum of ellipsoids". In Proc. of the 57th IEEE Conference on Decision and
      Control (CDC), pp. 4040-4045, 2018. arXiv:1803.08157.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 5], [1, Eq. 6]: the shape form and the `(A, b, c)` form denote the same ellipsoid. -/
theorem Ellipsoid.quadratic_form_equiv {Q : Matrix n n ℝ} (hQ : Q.PosDef) (q x : n → ℝ) :
    ((x - q) ⬝ᵥ Q⁻¹ *ᵥ (x - q) ≤ 1
      ↔ x ⬝ᵥ Q⁻¹ *ᵥ x + 2 * (x ⬝ᵥ (-(Q⁻¹ *ᵥ q))) + (q ⬝ᵥ Q⁻¹ *ᵥ q - 1) ≤ 0)
    ∧ (Q⁻¹)⁻¹ = Q ∧ -(Q *ᵥ (-(Q⁻¹ *ᵥ q))) = q := by -- --- PROOF ---
  have hA : (Q⁻¹).IsHermitian := hQ.inv.isHermitian
  have hu : IsUnit Q.det := (isUnit_iff_isUnit_det Q).1 hQ.isUnit
  -- `Q⁻¹` is symmetric, so the two cross terms are equal
  have hsym : ∀ u v : n → ℝ, u ⬝ᵥ Q⁻¹ *ᵥ v = v ⬝ᵥ Q⁻¹ *ᵥ u := by
    intro u v
    rw [dotProduct_mulVec, dotProduct_comm]
    have h := hA.eq
    simp only [conjTranspose_eq_transpose_of_trivial] at h
    rw [← mulVec_transpose, h]
  refine ⟨?_, nonsing_inv_nonsing_inv Q hu, ?_⟩
  · rw [mulVec_sub, dotProduct_sub, sub_dotProduct, sub_dotProduct, hsym q x, dotProduct_neg]
    constructor <;> intro h <;> nlinarith [h]
  · rw [mulVec_neg, mulVec_mulVec, mul_nonsing_inv Q hu, one_mulVec, neg_neg]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
