module

public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# A diagonal of a box lies in the box of the stored diagonals

A real vector between the stored bounds `lo` and `hi` has its diagonal matrix between the stored
diagonal blocks `diagonalBlock lo` and `diagonalBlock hi`: on the diagonal the bounds are the
vector's, off it every entry is the exact zero.

## Inputs
* `n` – vector width
* `lo` – lower bounds
* `hi` – upper bounds
* `v` – real vector

## Hypotheses
* `hv` – the vector lies between the bounds

## Conclusion
* the diagonal matrix lies in the box of the diagonal blocks
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.diagonal_mem {n : ℕ} (lo hi : Vec 𝕋 n) (v : Vec ℝ n)
    (hv : v ∈ (⟨lo, hi⟩ : Interval (Vec 𝕋 n)).construct) : -- --- CONCL ---
    Matrix.diagonal v ∈
      (⟨diagonalBlock lo, diagonalBlock hi⟩ : Interval (Mat 𝕋 n n)).construct := by -- --- PROOF ---
  refine Interval.mem_mat_iff.mpr fun i j => ?_
  by_cases hij : i = j
  · -- on the diagonal the bounds are the vector's
    subst hij
    have h : toRealVec lo i ≤ v i ∧ v i ≤ toRealVec hi i := hv i
    refine ⟨?_, ?_⟩
    · show toReal (diagonalBlock lo i i) ≤ Matrix.diagonal v i i
      rw [toReal_diagonalBlock]; simp only [Matrix.diagonal_apply_eq]; exact h.1
    · show Matrix.diagonal v i i ≤ toReal (diagonalBlock hi i i)
      rw [toReal_diagonalBlock]; simp only [Matrix.diagonal_apply_eq]; exact h.2
  · -- off it every entry is the exact zero
    refine ⟨?_, ?_⟩
    · show toReal (diagonalBlock lo i j) ≤ Matrix.diagonal v i j
      rw [toReal_diagonalBlock, Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ hij]
    · show Matrix.diagonal v i j ≤ toReal (diagonalBlock hi i j)
      rw [toReal_diagonalBlock, Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ hij]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
