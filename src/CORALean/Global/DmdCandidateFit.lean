import CORALean.Global.DmdCandidate

/-!
# The full-rank candidate fits consistent data exactly

If `X2 = G X1` for some `G` — the data was produced by a map of the regressors — and
`X1 = V S Wᵀ` with orthonormal `V`, `W` and nonzero `s`, the candidate of full rank `r`
satisfies `M X1 = X2`: `X2 W S⁻¹ Vᵀ V S Wᵀ = X2 W Wᵀ = G V S Wᵀ W Wᵀ = X2`. No claim for
lower ranks, nor that the fit is the least-squares one when the data is not consistent.
The source is [1]; without input it is the claim of [2, Eq. 7] that `X' Ṽ Σ̃⁻¹ Ũᵀ` recovers `A`
from the snapshots of `x_{k+1} = A x_k`.

## References

* [1] `contDynamics/@linearSysDT/private/priv_identifyDMD.m`
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

variable {n p N r : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem dmdCandidate_mul_eq (X1 : Mat ℝ p N) (X2 : Mat ℝ n N) (V : Mat ℝ p r) (s : Fin r → ℝ)
    (W : Mat ℝ N r) (hX1 : X1 = V * Matrix.diagonal s * Wᵀ) (hV : Vᵀ * V = 1)
    (hW : Wᵀ * W = 1) (hs : ∀ i, s i ≠ 0) (G : Mat ℝ n p) (hG : X2 = G * X1) :
    dmdCandidate X2 V s W r * X1 = X2 := by -- --- PROOF ---
  -- at full rank the cut-off is vacuous, so the middle factor is the inverse of `diag s`
  have hdiag : Matrix.diagonal (fun i : Fin r => if (i : ℕ) < r then (s i)⁻¹ else 0)
      * Matrix.diagonal s = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    simp [i.isLt, inv_mul_cancel₀ (hs i)]
  -- `X2 W Wᵀ = X2`, the rows of `X2` lying in the row space of `X1`
  have hWW : X2 * W * Wᵀ = X2 := by
    rw [hG, hX1]
    calc G * (V * Matrix.diagonal s * Wᵀ) * W * Wᵀ
        = G * (V * Matrix.diagonal s * (Wᵀ * W)) * Wᵀ := by simp only [Matrix.mul_assoc]
      _ = G * (V * Matrix.diagonal s * Wᵀ) := by rw [hW]; simp [Matrix.mul_assoc]
  unfold dmdCandidate
  rw [hX1]
  calc X2 * W * Matrix.diagonal (fun i : Fin r => if (i : ℕ) < r then (s i)⁻¹ else 0) * Vᵀ
        * (V * Matrix.diagonal s * Wᵀ)
      = X2 * W * (Matrix.diagonal (fun i : Fin r => if (i : ℕ) < r then (s i)⁻¹ else 0)
        * ((Vᵀ * V) * Matrix.diagonal s)) * Wᵀ := by simp only [Matrix.mul_assoc]
    _ = X2 := by rw [hV, Matrix.one_mul, hdiag, Matrix.mul_one, hWW]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
