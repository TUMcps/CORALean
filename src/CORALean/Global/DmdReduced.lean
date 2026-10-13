module

public import CORALean.Global.DmdCandidate

@[expose] public section

/-!
# The reduced-order matrix and the dynamic modes of the dynamic mode decomposition

With the economy SVD `X = Ũ Σ̃ Ṽᵀ`, `Ā = X' Ṽ Σ̃⁻¹ Ũᵀ` [1, Eq. 7] and its reduced-order
counterpart `Ã = Ũᵀ X' Ṽ Σ̃⁻¹`: `Ã = Ũᵀ Ā Ũ`, the projection `x = Ũ x̃` [1, Eq. 9-12]. The
dynamic modes `φ = X' Ṽ Σ̃⁻¹ w` of an eigenpair `Ã w = λ w` [1, Eq. 13] satisfy `Ā φ = λ φ`,
and `φ ≠ 0` for `λ ≠ 0`. With a known input matrix `X'` is replaced by `X' - B Υ`
[1, Eq. 20-23, Eq. 24]; every statement is for any right-hand matrix `X2`. For
`Ã w = 0` the mode `Ũ w` the paper prescribes is no eigenvector of `Ā` in general; see
`dmd_zeroMode_counterexample`. Real eigenpairs only: the paper's `λ`, `w` are complex.

## References

* [1] J. L. Proctor, S. L. Brunton and J. N. Kutz. "Dynamic mode decomposition with control".
      SIAM Journal on Applied Dynamical Systems, 15(1):142-161, 2016 (arXiv:1409.6358).
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n p N r k : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 9-12], [1, Eq. 20-23]: `Ũᵀ Ā Ũ = Ũᵀ X2 Ṽ Σ̃⁻¹`, for `ŨᵀŨ = I`. -/
theorem dmdCandidate_reduced (X2 : Mat ℝ n N) (V : Mat ℝ n r) (s : Fin r → ℝ) (W : Mat ℝ N r)
    (hV : Vᵀ * V = 1) :
    Vᵀ * dmdCandidate X2 V s W r * V
      = Vᵀ * (X2 * W * Matrix.diagonal
        (fun i : Fin r => if (i : ℕ) < r then (s i)⁻¹ else 0)) := by -- --- PROOF ---
  unfold dmdCandidate
  calc Vᵀ * (X2 * W * Matrix.diagonal (fun i : Fin r => if (i : ℕ) < r then (s i)⁻¹ else 0)
        * Vᵀ) * V
      = Vᵀ * (X2 * W * Matrix.diagonal (fun i : Fin r => if (i : ℕ) < r then (s i)⁻¹ else 0))
        * (Vᵀ * V) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hV, Matrix.mul_one]

/-- [1, Eq. 13], [1, Eq. 24]: with `Ā = K Z` and `Ã = Z K` (`K = X2 Ṽ Σ̃⁻¹`, `Z = Ũᵀ`), the
columns of `K W` are eigenvectors of `Ā` for the eigenpairs of `Ã`. -/
theorem dmd_mode_matrix (K : Mat ℝ n r) (Z : Mat ℝ r n) (W : Mat ℝ r k) (Λ : Mat ℝ k k)
    (h : (Z * K) * W = W * Λ) : (K * Z) * (K * W) = (K * W) * Λ := by
  calc K * Z * (K * W) = K * ((Z * K) * W) := by simp only [Matrix.mul_assoc]
    _ = K * (W * Λ) := by rw [h]
    _ = K * W * Λ := by rw [Matrix.mul_assoc]

/-- [1, Eq. 13], [1, Eq. 24]: one eigenpair `Ã w = λ w`; the mode `K w` is an eigenvector of `Ā`,
and nonzero when `λ ≠ 0` and `w ≠ 0`. -/
theorem dmd_mode_vec (K : Mat ℝ n r) (Z : Mat ℝ r n) (w : Vec ℝ r) (lam : ℝ)
    (h : (Z * K) *ᵥ w = lam • w) :
    (K * Z) *ᵥ (K *ᵥ w) = lam • (K *ᵥ w) ∧ (lam ≠ 0 → w ≠ 0 → K *ᵥ w ≠ 0) := by -- --- PROOF ---
  refine ⟨?_, fun hl hw hKw => ?_⟩
  · rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul]
  · have hZ : lam • w = 0 := by
      rw [← h, ← Matrix.mulVec_mulVec, hKw, Matrix.mulVec_zero]
    exact (smul_eq_zero.mp hZ).elim hl hw

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
