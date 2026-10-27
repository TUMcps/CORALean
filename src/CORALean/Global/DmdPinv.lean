module

public import CORALean.Global.DmdCandidate

@[expose] public section

/-!
# The SVD factors give the Moore-Penrose pseudo-inverse

[1, Eq. 4]: `A = X' X†` with `†` the Moore-Penrose pseudo-inverse, computed through the SVD
`X = Ũ Σ̃ Ṽᵀ` [1, Eq. 7] as `X† = Ṽ Σ̃⁻¹ Ũᵀ`. The pseudo-inverse is the matrix satisfying the
four Penrose conditions, which determine it uniquely; `W S⁻¹ Vᵀ` satisfies them for the
economy SVD `X = V S Wᵀ` of full rank `r`, so `dmdCandidate X' V s W r` is `X' X†`. The paper
truncates the SVD at a rank `r` below the full one, which is no pseudo-inverse of `X`; only
the full-rank case is here.

## Inputs
* `X` – matrix
* `P` – candidate pseudo-inverse

## Output
* the proposition that the candidate satisfies the four Penrose conditions

## References

* [1] [J. L. Proctor, S. L. Brunton and J. N. Kutz. "Dynamic Mode Decomposition with Control". SIAM
      Journal on Applied Dynamical Systems,
      2016.](../../../references/2016/proctor-siads-dmd-control.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {p N r n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The four Penrose conditions: `P` is the Moore-Penrose pseudo-inverse of `X`. -/
def IsPinv (X : Mat ℝ p N) (P : Mat ℝ N p) : Prop :=
  X * P * X = X ∧ P * X * P = P ∧ (X * P)ᵀ = X * P ∧ (P * X)ᵀ = P * X

/-- The pseudo-inverse is unique. -/
theorem IsPinv.unique {X : Mat ℝ p N} {P Q : Mat ℝ N p} (hP : IsPinv X P)
    (hQ : IsPinv X Q) : -- --- CONCL ---
    P = Q := by -- --- PROOF ---
  obtain ⟨hP1, hP2, hP3, hP4⟩ := hP
  obtain ⟨hQ1, hQ2, hQ3, hQ4⟩ := hQ
  -- `P X = Q X`: `P X = (P X)(Q X) = ((P X)ᵀ (Q X)ᵀ) = (Q X P X)ᵀ = (Q X)ᵀ`
  have e1 : P * X = Q * X := by
    calc P * X = P * (X * Q * X) := by rw [hQ1]
      _ = (P * X) * (Q * X) := by simp only [Matrix.mul_assoc]
      _ = (P * X)ᵀ * (Q * X)ᵀ := by rw [hP4, hQ4]
      _ = (Q * X * (P * X))ᵀ := (Matrix.transpose_mul _ _).symm
      _ = (Q * (X * P * X))ᵀ := by simp only [Matrix.mul_assoc]
      _ = (Q * X)ᵀ := by rw [hP1]
      _ = Q * X := hQ4
  -- `X P = X Q` likewise
  have e2 : X * P = X * Q := by
    calc X * P = (X * Q * X) * P := by rw [hQ1]
      _ = (X * Q) * (X * P) := by simp only [Matrix.mul_assoc]
      _ = (X * Q)ᵀ * (X * P)ᵀ := by rw [hP3, hQ3]
      _ = (X * P * (X * Q))ᵀ := (Matrix.transpose_mul _ _).symm
      _ = ((X * P * X) * Q)ᵀ := by simp only [Matrix.mul_assoc]
      _ = (X * Q)ᵀ := by rw [hP1]
      _ = X * Q := hQ3
  calc P = P * X * P := hP2.symm
    _ = Q * X * P := by rw [e1]
    _ = Q * (X * P) := Matrix.mul_assoc _ _ _
    _ = Q * (X * Q) := by rw [e2]
    _ = Q * X * Q := (Matrix.mul_assoc _ _ _).symm
    _ = Q := hQ2

/-- `W S⁻¹ Vᵀ` is the pseudo-inverse of `X = V S Wᵀ` for orthonormal `V`, `W` and `s ≠ 0`. -/
theorem isPinv_svd (X : Mat ℝ p N) (V : Mat ℝ p r) (s : Fin r → ℝ) (W : Mat ℝ N r)
    (hX : X = V * Matrix.diagonal s * Wᵀ) (hV : Vᵀ * V = 1) (hW : Wᵀ * W = 1)
    (hs : ∀ i, s i ≠ 0) : -- --- CONCL ---
    IsPinv X (W * Matrix.diagonal (fun i => (s i)⁻¹) * Vᵀ) := by -- --- PROOF ---
  -- the diagonal factors are inverse to each other
  have hDD : Matrix.diagonal s * Matrix.diagonal (fun i => (s i)⁻¹) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; exact mul_inv_cancel₀ (hs i)
  have hDD' : Matrix.diagonal (fun i => (s i)⁻¹) * Matrix.diagonal s = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; exact inv_mul_cancel₀ (hs i)
  -- `X P = V Vᵀ` and `P X = W Wᵀ`, which are symmetric
  have hXP : X * (W * Matrix.diagonal (fun i => (s i)⁻¹) * Vᵀ) = V * Vᵀ := by
    rw [hX]
    calc V * Matrix.diagonal s * Wᵀ * (W * Matrix.diagonal (fun i => (s i)⁻¹) * Vᵀ)
        = V * Matrix.diagonal s * ((Wᵀ * W) * Matrix.diagonal (fun i => (s i)⁻¹)) * Vᵀ := by
          simp only [Matrix.mul_assoc]
      _ = V * Vᵀ := by rw [hW, Matrix.one_mul, Matrix.mul_assoc V, hDD, Matrix.mul_one]
  have hPX : (W * Matrix.diagonal (fun i => (s i)⁻¹) * Vᵀ) * X = W * Wᵀ := by
    rw [hX]
    calc W * Matrix.diagonal (fun i => (s i)⁻¹) * Vᵀ * (V * Matrix.diagonal s * Wᵀ)
        = W * (Matrix.diagonal (fun i => (s i)⁻¹) * ((Vᵀ * V) * Matrix.diagonal s)) * Wᵀ := by
          simp only [Matrix.mul_assoc]
      _ = W * Wᵀ := by rw [hV, Matrix.one_mul, hDD', Matrix.mul_one]
  -- the four conditions
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hXP, hX]
    calc V * Vᵀ * (V * Matrix.diagonal s * Wᵀ)
        = V * ((Vᵀ * V) * Matrix.diagonal s) * Wᵀ := by simp only [Matrix.mul_assoc]
      _ = V * Matrix.diagonal s * Wᵀ := by rw [hV, Matrix.one_mul]
  · rw [hPX]
    calc W * Wᵀ * (W * Matrix.diagonal (fun i => (s i)⁻¹) * Vᵀ)
        = W * ((Wᵀ * W) * Matrix.diagonal (fun i => (s i)⁻¹)) * Vᵀ := by
          simp only [Matrix.mul_assoc]
      _ = W * Matrix.diagonal (fun i => (s i)⁻¹) * Vᵀ := by rw [hW, Matrix.one_mul]
  · rw [hXP, Matrix.transpose_mul, Matrix.transpose_transpose]
  · rw [hPX, Matrix.transpose_mul, Matrix.transpose_transpose]

/-- [1, Eq. 4] with [1, Eq. 7] at full rank: `X' Ṽ Σ̃⁻¹ Ũᵀ = X' X†`. -/
theorem dmdCandidate_eq_mul_pinv (X2 : Mat ℝ n N) (X : Mat ℝ p N) (V : Mat ℝ p r)
    (s : Fin r → ℝ) (W : Mat ℝ N r) (hX : X = V * Matrix.diagonal s * Wᵀ) (hV : Vᵀ * V = 1)
    (hW : Wᵀ * W = 1) (hs : ∀ i, s i ≠ 0) (P : Mat ℝ N p) (hP : IsPinv X P) : -- --- CONCL ---
    dmdCandidate X2 V s W r = X2 * P := by -- --- PROOF ---
  rw [← IsPinv.unique (isPinv_svd X V s W hX hV hW hs) hP]
  unfold dmdCandidate
  have : (fun i : Fin r => if (i : ℕ) < r then (s i)⁻¹ else 0) = fun i => (s i)⁻¹ := by
    funext i; simp [i.isLt]
  rw [this]
  simp only [Matrix.mul_assoc]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
