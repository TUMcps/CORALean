import CORALean.Global.DmdPinv
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# The pseudo-inverse of a matrix that is onto

For `H` with `H *ᵥ ·` onto, `H Hᵀ` is invertible and `Hᵀ (H Hᵀ)⁻¹` satisfies the four Penrose
conditions (`IsPinv`). Invertibility is read off the kernel: `H Hᵀ v = 0` gives
`‖Hᵀ v‖² = vᵀ H Hᵀ v = 0`, so `v` is orthogonal to `Im H`, which is everything, and `v = 0`.
With `H Hᵀ (H Hᵀ)⁻¹ = 1` the conditions are a line each; the last uses that the inverse of
the symmetric `H Hᵀ` is symmetric.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n l : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- For `H` onto, `H Hᵀ` has a unit determinant. -/
theorem aux_isUnit_det_mul_transpose (H : Mat ℝ n l) (hH : Function.Surjective H.mulVec) :
    IsUnit (H * Hᵀ).det := by -- --- PROOF ---
  rw [← isUnit_iff_isUnit_det, ← mulVec_injective_iff_isUnit]
  intro a b hab
  -- `v = a - b` has `H Hᵀ v = 0`, so `Hᵀ v = 0`, so `v ⟂ Im H = ℝⁿ`
  have hv : (H * Hᵀ) *ᵥ (a - b) = 0 := by rw [mulVec_sub, hab, sub_self]
  have hHt : Hᵀ *ᵥ (a - b) = 0 := by
    apply dotProduct_self_eq_zero.mp
    rw [mulVec_transpose, ← dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, hv,
      dotProduct_zero]
  obtain ⟨β, hβ⟩ := hH (a - b)
  have : (a - b) ⬝ᵥ (a - b) = 0 := by
    conv_rhs => rw [← zero_dotProduct β, ← hHt]
    rw [mulVec_transpose, ← dotProduct_mulVec, hβ]
  exact sub_eq_zero.mp (dotProduct_self_eq_zero.mp this)


-- =======================================  MAIN THEOREM  ======================================= --

/-- For `H` onto, `Hᵀ (H Hᵀ)⁻¹` is the Moore-Penrose pseudo-inverse of `H`. -/
theorem isPinv_of_surjective (H : Mat ℝ n l) (hH : Function.Surjective H.mulVec) :
    IsPinv H (Hᵀ * (H * Hᵀ)⁻¹) := by -- --- PROOF ---
  have hu := aux_isUnit_det_mul_transpose H hH
  have hone : H * (Hᵀ * (H * Hᵀ)⁻¹) = 1 := by rw [← Matrix.mul_assoc, mul_nonsing_inv _ hu]
  have hsym : ((H * Hᵀ)⁻¹)ᵀ = (H * Hᵀ)⁻¹ := by
    rw [transpose_nonsing_inv, transpose_mul, transpose_transpose]
  refine ⟨by rw [hone, Matrix.one_mul], ?_, by rw [hone, transpose_one], ?_⟩
  · rw [Matrix.mul_assoc, hone, Matrix.mul_one]
  · rw [transpose_mul, transpose_mul, hsym, transpose_transpose, Matrix.mul_assoc]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
