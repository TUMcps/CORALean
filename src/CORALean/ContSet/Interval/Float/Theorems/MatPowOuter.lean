import CORALean.ContSet.Interval.Float.Operations.MatPow
import CORALean.ContSet.Interval.Float.Theorems.MatMulOuter
import CORALean.ContSet.Interval.Float.Theorems.MemPoint

/-!
# `Interval.matPow` encloses every power of a matrix in the box

Induction on `k`, unfolding `matPow`'s right recursion with `pow_succ'` against
`matMul_outer` and the induction hypothesis, exactly as `Real.Interval.
matPow_outer` does; the base case is `mem_point` at the stored identity block,
read back as `(1 : Mat ℝ n n)`.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


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
  | succ k ih => rw [pow_succ']; exact Interval.matMul_outer A (A.matPow k) hM ih

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
