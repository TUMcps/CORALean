import CORALean.Global.LeastSquaresOfNormalEq
import CORALean.Global.DmdCandidate
import Mathlib.Data.Matrix.Diagonal

/-!
# The SVD solution is a least-squares fit

[1, Eq. 6]: `A = Ẋ V Σ⁻¹ Uᵀ` for the SVD `Φ = U Σ Vᵀ` solves (4), and [1, Eq. 17], the
reset fit, the same way. With the economy SVD (`UᵀU = I`, `VᵀV = I`, `Σ = diag(s)`, `s ≠ 0`,
`r` the rank) this is `dmdCandidate Ẋ U s V r`, CORA's `aux_dynamicModeDecomposition` at full
rank and `priv_identifyDMD` for `linearSys`/`linearSysDT`: `A Φ = Ẋ V Vᵀ`, so
`(Ẋ - A Φ) Φᵀ = (Ẋ V - Ẋ V Vᵀ V) Σ Uᵀ = 0`, the normal equations. No full row rank of `Φ` is
needed; the rank-adapted candidates (fewer singular values) are not least-squares fits. The
same formula is [2, Eq. 7], `A ≈ X' Ṽ Σ̃⁻¹ Ũᵀ`, for the snapshots of `x_{k+1} = A x_k`.

## References

* [1] N. Kochdumper, M. A. Foughali, P. Habermehl and E. Asarin. "Robust Identification of
      Hybrid Automata from Noisy Data". In Proc. of the 28th ACM International Conference on
      Hybrid Systems: Computation and Control (HSCC), pp. 1-11, 2025.
* [2] J. L. Proctor, S. L. Brunton and J. N. Kutz. "Dynamic mode decomposition with control".
      SIAM Journal on Applied Dynamical Systems, 15(1):142-161, 2016 (arXiv:1409.6358).
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n v N r : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 6]: `Ẋ V Σ⁻¹ Uᵀ` minimizes (4) for the economy SVD `Φ = U Σ Vᵀ`. -/
theorem dmdCandidate_leastSquares (Xd : Mat ℝ n N) (Φ : Mat ℝ v N) (U : Mat ℝ v r)
    (s : Fin r → ℝ) (V : Mat ℝ N r) (hΦ : Φ = U * Matrix.diagonal s * Vᵀ) (hU : Uᵀ * U = 1)
    (hV : Vᵀ * V = 1) (hs : ∀ i, s i ≠ 0) (B : Mat ℝ n v) :
    ∑ i, ∑ a, ((Xd - dmdCandidate Xd U s V r * Φ) a i) ^ 2
      ≤ ∑ i, ∑ a, ((Xd - B * Φ) a i) ^ 2 := by -- --- PROOF ---
  refine leastSquares_le_of_normal_eq Xd Φ _ ?_ B
  -- at full rank the middle factor inverts `diag(s)`
  have hdiag : Matrix.diagonal (fun i : Fin r => if (i : ℕ) < r then (s i)⁻¹ else 0)
      * Matrix.diagonal s = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    simp [i.isLt, inv_mul_cancel₀ (hs i)]
  -- `A Φ = Ẋ V Vᵀ`
  have hAΦ : dmdCandidate Xd U s V r * Φ = Xd * V * Vᵀ := by
    unfold dmdCandidate
    rw [hΦ]
    calc Xd * V * Matrix.diagonal (fun i : Fin r => if (i : ℕ) < r then (s i)⁻¹ else 0) * Uᵀ
          * (U * Matrix.diagonal s * Vᵀ)
        = Xd * V * (Matrix.diagonal (fun i : Fin r => if (i : ℕ) < r then (s i)⁻¹ else 0)
          * ((Uᵀ * U) * Matrix.diagonal s)) * Vᵀ := by simp only [Matrix.mul_assoc]
      _ = Xd * V * Vᵀ := by rw [hU, Matrix.one_mul, hdiag, Matrix.mul_one]
  -- `(Ẋ - Ẋ V Vᵀ) V = 0`, and `Φᵀ = V Σ Uᵀ` starts with `V`
  rw [hAΦ, hΦ, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.diagonal_transpose]
  calc (Xd - Xd * V * Vᵀ) * (V * (Matrix.diagonal s * Uᵀ))
      = (Xd * V - Xd * V * (Vᵀ * V)) * (Matrix.diagonal s * Uᵀ) := by
        simp only [Matrix.sub_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hV, Matrix.mul_one, sub_self, Matrix.zero_mul]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
