module

public import CORALean.Global.Tensor
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# An orthogonal matrix with a given first column

Every unit vector `u` is the first column of an orthogonal matrix: the Householder reflection
`B = I - (2 / wᵀw) w wᵀ` with `w = u - e₀` is symmetric, squares to `I`, and carries `e₀` to `u`
(`wᵀw = 2 - 2 u₀` and `wᵀe₀ = u₀ - 1`, so `(2 / wᵀw) w₀ = -1`). When `u = e₀` the identity does.

## Inputs
* `n` – dimension
* `u` – unit vector

## Hypotheses
* `hu` – the vector has unit length

## Conclusion
* an orthogonal matrix has the vector as its first column
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem exists_orthogonal_firstCol {n : ℕ} [NeZero n] (u : Vec ℝ n)
    (hu : u ⬝ᵥ u = 1) : -- --- CONCL ---
    ∃ B : Mat ℝ n n, B * Bᵀ = 1 ∧ ∀ j, B j 0 = u j := by -- --- PROOF ---
  classical
  -- the first unit vector
  set e : Vec ℝ n := fun j => if j = 0 then 1 else 0 with he
  by_cases hue : u = e
  · refine ⟨1, by simp, fun j => ?_⟩
    simp [Matrix.one_apply, hue, he]
  -- the reflection through the hyperplane orthogonal to `w = u - e`
  set w : Vec ℝ n := u - e with hw
  have hee : e ⬝ᵥ e = 1 := by simp [he, dotProduct, Finset.sum_ite_eq']
  have hue0 : u ⬝ᵥ e = u 0 := by simp [he, dotProduct, Finset.sum_ite_eq']
  have hww : w ⬝ᵥ w = 2 - 2 * u 0 := by
    simp only [hw, sub_dotProduct, dotProduct_sub, hu, hee, hue0, dotProduct_comm e u]
    ring
  have hne : w ⬝ᵥ w ≠ 0 := fun h => hue (sub_eq_zero.mp (dotProduct_self_eq_zero.mp h))
  set c : ℝ := 2 / (w ⬝ᵥ w) with hc
  have hcw : c * (w ⬝ᵥ w) = 2 := by rw [hc]; field_simp
  refine ⟨(1 : Mat ℝ n n) - c • vecMulVec w w, ?_, fun j => ?_⟩
  · -- symmetric, and a reflection squares to the identity
    have hT : ((1 : Mat ℝ n n) - c • vecMulVec w w)ᵀ = (1 : Mat ℝ n n) - c • vecMulVec w w := by
      simp [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_vecMulVec]
    have hWW : vecMulVec w w * vecMulVec w w = (w ⬝ᵥ w) • vecMulVec w w := by
      rw [Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_smul]
    rw [hT]
    simp only [sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, hWW, smul_smul]
    -- `c (wᵀw) = 2`, so the two rank-one terms cancel
    rw [hcw]
    module
  · -- the first column is `e - c w₀ w`, and `c w₀ = -1`
    have hw0 : w 0 = u 0 - 1 := by simp [hw, he]
    have hcw0 : c * w 0 = -1 := by
      have : w ⬝ᵥ w = -2 * w 0 := by rw [hww, hw0]; ring
      rw [hc, this]
      have : w 0 ≠ 0 := fun h => hne (by rw [‹w ⬝ᵥ w = -2 * w 0›, h]; ring)
      field_simp
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Matrix.one_apply,
      smul_eq_mul]
    have : c * (w j * w 0) = -w j := by rw [mul_left_comm, hcw0]; ring
    rw [this]
    simp [hw, he]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
