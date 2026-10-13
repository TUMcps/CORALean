import CORALean.Global.LeastSquaresOfNormalEq
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The pseudo-inverse solution, with the Gram matrix of the right side

[1, Eq. 5] prints `A = Ẋ (Φᵀ Φ)⁻¹ Φᵀ` for `Φ = [φ(x(t_{j-w}), u(t_{j-w})), …]`, one column per
data point. That is the formula for data in rows; with data in columns, as the paper stacks
them, `Φᵀ Φ` is `(2w + 1) × (2w + 1)` of rank at most `v` and singular whenever `2w + 1 > v`
(`det_transpose_mul_self_eq_zero`), which the paper's own grid for `w` makes the rule. The
solution of (4) is `A = Ẋ Φᵀ (Φ Φᵀ)⁻¹` when `Φ Φᵀ` is invertible: it solves the normal
equations, so `leastSquares_le_of_normal_eq` applies.

## References

* [1] N. Kochdumper, M. A. Foughali, P. Habermehl and E. Asarin. "Robust Identification of
      Hybrid Automata from Noisy Data". In Proc. of the 28th ACM International Conference on
      Hybrid Systems: Computation and Control (HSCC), pp. 1-11, 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n v N : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 5], corrected: `A = Ẋ Φᵀ (Φ Φᵀ)⁻¹` minimizes (4) when `det(Φ Φᵀ) ≠ 0`. -/
theorem pinv_leastSquares (Xd : Mat ℝ n N) (Φ : Mat ℝ v N) (hΦ : (Φ * Φᵀ).det ≠ 0)
    (B : Mat ℝ n v) :
    ∑ i, ∑ a, ((Xd - Xd * Φᵀ * (Φ * Φᵀ)⁻¹ * Φ) a i) ^ 2 ≤ ∑ i, ∑ a, ((Xd - B * Φ) a i) ^ 2 := by
  refine leastSquares_le_of_normal_eq Xd Φ _ ?_ B
  have hinv : (Φ * Φᵀ)⁻¹ * (Φ * Φᵀ) = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hΦ)
  rw [Matrix.sub_mul, Matrix.mul_assoc (Xd * Φᵀ * (Φ * Φᵀ)⁻¹), Matrix.mul_assoc (Xd * Φᵀ), hinv,
    Matrix.mul_one, sub_self]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
