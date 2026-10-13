import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Spectrum

/-!
# A positive-definite times a symmetric matrix is diagonalizable

[1, Lemma 1]: for symmetric `M₂` and positive-definite `M₁`, `M₁ M₂` is diagonalizable. The
printed proof takes the positive square root `N` of `M₁` and sees that `N⁻¹ (M₁ M₂) N =
N M₂ N` is symmetric; here the symmetric matrix is diagonalized by the spectral theorem,
`N M₂ N = U Λ Uᴴ`, and `M₁ M₂ = (N U) Λ (N U)⁻¹`. When `M₂` is positive definite so is
`N M₂ N`, and the diagonal entries are positive, which [1, Prop. 1] needs.

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
open scoped MatrixOrder

variable {n : Type*} [Fintype n] [DecidableEq n]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Lemma 1]: `M₁ M₂ = S diag(d) T`, `S T = 1`, with `d > 0` when `M₂` is positive definite. -/
theorem Ellipsoid.halder_diagonalizable {M₁ M₂ : Matrix n n ℝ} (h₁ : M₁.PosDef)
    (h₂ : M₂.IsHermitian) :
    ∃ (S T : Matrix n n ℝ) (d : n → ℝ), S * T = 1 ∧ T * S = 1 ∧
      M₁ * M₂ = S * diagonal d * T ∧ (M₂.PosDef → ∀ i, 0 < d i) := by -- --- PROOF ---
  -- the positive root `N` of `M₁` turns `M₁ M₂` into the symmetric `N M₂ N`
  set N : Matrix n n ℝ := CFC.sqrt M₁ with hNdef
  have hNN : N * N = M₁ := CFC.sqrt_mul_sqrt_self M₁ h₁.posSemidef.nonneg
  have hNh : N.IsHermitian := (CFC.sqrt_nonneg M₁).posSemidef.isHermitian
  have hNu : IsUnit N := by
    have : IsUnit (N * N) := hNN ▸ h₁.isUnit
    exact (isUnit_iff_isUnit_det N).2 (by
      rw [isUnit_iff_isUnit_det, det_mul] at this
      exact (IsUnit.mul_iff.1 this).1)
  set K : Matrix n n ℝ := N * M₂ * N with hK
  have hKh : K.IsHermitian := by
    unfold IsHermitian
    simp only [hK, conjTranspose_mul, hNh.eq, h₂.eq, mul_assoc]
  -- the spectral theorem for `K`
  set U : Matrix n n ℝ := (hKh.eigenvectorUnitary : Matrix n n ℝ) with hU
  have hUU : U * star U = 1 := Unitary.coe_mul_star_self hKh.eigenvectorUnitary
  have hUU' : star U * U = 1 := Unitary.coe_star_mul_self hKh.eigenvectorUnitary
  have hspec : K = U * diagonal hKh.eigenvalues * star U := by
    have := hKh.spectral_theorem
    simpa [Unitary.conjStarAlgAut_apply] using this
  have hdet : IsUnit N.det := (isUnit_iff_isUnit_det N).1 hNu
  have hNi : N * N⁻¹ = 1 := mul_nonsing_inv N hdet
  have hNi' : N⁻¹ * N = 1 := nonsing_inv_mul N hdet
  refine ⟨N * U, star U * N⁻¹, hKh.eigenvalues, ?_, ?_, ?_, ?_⟩
  · calc N * U * (star U * N⁻¹) = N * (U * star U) * N⁻¹ := by simp only [mul_assoc]
      _ = 1 := by rw [hUU, mul_one, hNi]
  · calc star U * N⁻¹ * (N * U) = star U * (N⁻¹ * N) * U := by simp only [mul_assoc]
      _ = 1 := by rw [hNi', mul_one, hUU']
  · -- `M₁ M₂ = N K N⁻¹`, and `K` is its spectral decomposition
    have h1 : M₁ * M₂ = N * K * N⁻¹ := by
      calc M₁ * M₂ = N * (N * M₂) * (N * N⁻¹) := by rw [hNi, mul_one, ← hNN, mul_assoc]
        _ = N * (N * M₂ * N) * N⁻¹ := by simp only [mul_assoc]
        _ = N * K * N⁻¹ := rfl
    rw [h1]
    have h2 := congrArg (fun A => N * A * N⁻¹) hspec
    simp only [mul_assoc] at h2 ⊢
    exact h2
  · -- the eigenvalues of a positive-definite `K` are positive
    intro hM₂ i
    have hKpd : K.PosDef := by
      have := (hNu.posDef_star_left_conjugate_iff (x := M₂)).2 hM₂
      rw [star_eq_conjTranspose, hNh.eq] at this
      exact this
    exact hKpd.eigenvalues_pos i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
