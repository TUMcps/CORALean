module

public import CORALean.ContSet.Interval.Float.Operations.MatPow
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.ContSet.Interval.Float.Theorems.MatMulOuter
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint

@[expose] public section

/-!
# `Interval.matPow` encloses every power of a matrix in the box

Induction on `k`, unfolding `matPow`'s right recursion with `pow_succ'` against
`matMul_outer` and the induction hypothesis, exactly as `Real.Interval.
matPow_outer` does; the base case is `mem_point` at the stored identity block,
read back as `(1 : Mat ℝ n n)`.

## Inputs
* `A` – interval matrix
* `M` – member of the box
* `k` – exponent

## Hypotheses
* `hM` – `M` lies in `A`

## Conclusion
* the power `M ^ k` lies in the result
-/

-- Authors:       Claude Sonnet 5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The stored identity block reads back as the real identity matrix. -/
theorem aux_toRealMat_diagonalBlock_one :
    toRealMat (diagonalBlock fun _ : Fin n => (one : 𝕋)) = (1 : Mat ℝ n n) := by
  funext i j
  rw [toRealMat, toReal_diagonalBlock]
  simp [toRealVec, toReal_one, Matrix.one_apply, Matrix.diagonal_apply]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.matPow_outer (A : Interval (Mat 𝕋 n n)) {M : Mat ℝ n n}
    (hM : M ∈ A.construct) (k : ℕ) : M ^ k ∈ (Interval.matPow A k).construct := by -- --- PROOF ---
  induction k with
  | zero =>
    rw [pow_zero, ← aux_toRealMat_diagonalBlock_one (𝕋 := 𝕋)]
    exact Interval.mem_point (diagonalBlock fun _ : Fin n => (one : 𝕋))
  | succ k ih =>
    rw [pow_succ']
    show M * M ^ k ∈ (Interval.matMul A (Interval.matPow A k)).materialiseMat.construct
    rw [Interval.materialiseMat_eq]
    exact Interval.matMul_outer A (A.matPow k) hM ih

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
