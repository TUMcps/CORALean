module

public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpRemainderMatEntryLe
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpTaylor
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential

@[expose] public section

/-!
# An entry of `E(Δt,η)` under the scalar bound of a diagonally scaled matrix

For positive scales `s`, `N = S⁻¹|A|S` (`N_jk = |a_jk| s_k / s_j`, `S = diag s`) is nonnegative and
`|A| = S N S⁻¹`. The exponential and its Taylor sum commute with the similarity, so
`E_A(r,η) = S E_N(r,η) S⁻¹` entry by entry: `E_A jk = (s_j / s_k) E_N jk`, and `E_N jk` is under
`expRemainderBound (r N) η` (`expRemainderMat_entry_le_bound`, `|N| = N`). A scaling that balances
the rows and columns of `|A|` makes `‖r N‖` small where `‖r A‖` is not, as for a stiff oscillator.

## Inputs
* `A` – system matrix
* `r` – step length
* `η` – Taylor order
* `s` – positive scales
* `j` – row index
* `k` – column index

## Hypotheses
* `hs` – the scales are positive
* `hlt` – the norm of the scaled matrix is small enough for the Taylor order

## Conclusion
* the entry of the remainder matrix is under `s_j / s_k` times the scaled scalar bound
-/

-- Authors:       Claude Opus 5.5
-- Written:       17-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `S X S⁻¹` entry by entry, for `S = diag s` and `S' = diag (1/s)`. -/
private theorem MatExp.aux_conj_apply (s : Fin n → ℝ) (X : Mat ℝ n n) (j k : Fin n) :
    (diagonal s * X * diagonal (fun i => (s i)⁻¹)) j k = s j * X j k * (s k)⁻¹ := by
  simp [Matrix.mul_diagonal, Matrix.diagonal_mul]

/-- `diag s` has the inverse `diag (1/s)`. -/
private theorem MatExp.aux_inv_diagonal {s : Fin n → ℝ} (hs : ∀ i, 0 < s i) :
    (diagonal s)⁻¹ = diagonal fun i => (s i)⁻¹ := by
  refine Matrix.inv_eq_left_inv ?_
  rw [diagonal_mul_diagonal, ← diagonal_one]
  exact congrArg diagonal (funext fun i => inv_mul_cancel₀ (hs i).ne')

/-- `diag s` is a unit. -/
private theorem MatExp.aux_isUnit_diagonal {s : Fin n → ℝ} (hs : ∀ i, 0 < s i) :
    IsUnit (diagonal s) := by
  rw [Matrix.isUnit_iff_isUnit_det, det_diagonal]
  exact (Finset.prod_ne_zero_iff.mpr fun i _ => (hs i).ne').isUnit

/-- A power of a conjugate is the conjugate of the power. -/
private theorem MatExp.aux_conj_pow {s : Fin n → ℝ} (hs : ∀ i, 0 < s i) (X : Mat ℝ n n)
    (i : ℕ) : -- --- CONCL ---
    (diagonal s * X * (diagonal s)⁻¹) ^ i
      = diagonal s * X ^ i * (diagonal s)⁻¹ := by -- --- PROOF ---
  have hu : (diagonal s)⁻¹ * diagonal s = 1 :=
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (MatExp.aux_isUnit_diagonal hs))
  induction i with
  | zero => simp [Matrix.mul_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det _).mp (MatExp.aux_isUnit_diagonal hs))]
  | succ i ih =>
    rw [pow_succ, ih, pow_succ]
    calc diagonal s * X ^ i * (diagonal s)⁻¹ * (diagonal s * X * (diagonal s)⁻¹)
        = diagonal s * X ^ i * ((diagonal s)⁻¹ * diagonal s) * X * (diagonal s)⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hu, Matrix.mul_one]; simp only [Matrix.mul_assoc]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `E(r,η)_jk ≤ (s_j / s_k) · expRemainderBound (r N) η` with `N_jk = |a_jk| s_k / s_j`. -/
theorem MatExp.expRemainderMat_le_scaled (A : Mat ℝ n n) (r : ℝ) (η : ℕ) {s : Fin n → ℝ}
    (hs : ∀ i, 0 < s i)
    (hlt : ‖r • (Matrix.of fun j k => |A j k| * s k / s j : Mat ℝ n n)‖ / ((η : ℝ) + 2) < 1)
    (j k : Fin n) : -- --- CONCL ---
    MatExp.expRemainderMat A r η j k
      ≤ s j / s k * MatExp.expRemainderBound
        (r • (Matrix.of fun j k => |A j k| * s k / s j : Mat ℝ n n)) η := by -- --- PROOF ---
  have hb := MatExp.expRemainderMat_entry_le_bound (r := r)
    (Matrix.of fun j k => |A j k| * s k / s j : Mat ℝ n n) η hlt j k
  set N : Mat ℝ n n := Matrix.of fun j k => |A j k| * s k / s j with hN
  set V : Mat ℝ n n := diagonal s with hV
  have hVinv : V⁻¹ = diagonal fun i => (s i)⁻¹ := MatExp.aux_inv_diagonal hs
  -- `|A| = S N S⁻¹`
  have habs : MatExp.absMat A = V * N * V⁻¹ := by
    funext a b
    rw [hVinv, MatExp.aux_conj_apply]
    simp only [MatExp.absMat, hN, Matrix.of_apply]
    field_simp [(hs a).ne', (hs b).ne']
  -- `|N| = N`
  have hNabs : MatExp.absMat N = N := by
    funext a b
    simp only [MatExp.absMat, hN, Matrix.of_apply]
    exact abs_of_nonneg (div_nonneg (mul_nonneg (abs_nonneg _) (hs b).le) (hs a).le)
  -- the powers and the exponential commute with the similarity
  have hpow : ∀ i : ℕ, (r • MatExp.absMat A) ^ i = V * (r • N) ^ i * V⁻¹ := by
    intro i
    rw [habs, ← MatExp.aux_conj_pow hs, Matrix.mul_smul, Matrix.smul_mul]
  have hexp : exp (r • MatExp.absMat A) = V * exp (r • N) * V⁻¹ := by
    have h1 := hpow 1
    simp only [pow_one] at h1
    rw [h1]
    exact Matrix.exp_conj V _ (MatExp.aux_isUnit_diagonal hs)
  -- so does the remainder, and an entry is scaled by `s_j / s_k`
  have hconj : MatExp.expRemainderMat A r η = V * MatExp.expRemainderMat N r η * V⁻¹ := by
    rw [MatExp.expRemainderMat, MatExp.expRemainderMat, hNabs, MatExp.expTaylor,
      MatExp.expTaylor, hexp, Matrix.mul_sub, Matrix.sub_mul, Finset.mul_sum, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hpow i, Matrix.mul_smul, Matrix.smul_mul]
  have hentry : MatExp.expRemainderMat A r η j k
      = s j * MatExp.expRemainderMat N r η j k * (s k)⁻¹ := by
    rw [hconj, hVinv]
    exact MatExp.aux_conj_apply s _ j k
  -- the unscaled bound at `N`, scaled back
  have hR := le_trans (le_abs_self (MatExp.expRemainderMat N r η j k)) hb
  rw [hentry]
  have hsk := inv_pos.mpr (hs k)
  have h1 : s j * MatExp.expRemainderMat N r η j k
      ≤ s j * MatExp.expRemainderBound (r • N) η := mul_le_mul_of_nonneg_left hR (hs j).le
  have h2 := mul_le_mul_of_nonneg_right h1 hsk.le
  calc s j * MatExp.expRemainderMat N r η j k * (s k)⁻¹
      ≤ s j * MatExp.expRemainderBound (r • N) η * (s k)⁻¹ := h2
    _ = s j / s k * MatExp.expRemainderBound (r • N) η := by rw [div_eq_mul_inv]; ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
