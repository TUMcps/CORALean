module

public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import CORALean.Global.Tensor

@[expose] public section

/-!
# The `n`-dimensional cross product

[1, Def. 2]'s `nX`: the vector orthogonal to `n - 1` given vectors, built from the alternating
minors of the matrix holding them, one row dropped each time; what [1, Thm. 2] takes a facet
normal to be. Written at `Mat ℝ (n + 1) n` rather than the printed `Mat ℝ n (n - 1)`: the same
object with the ambient dimension named as a successor, so dropping a row lands in `Fin n` with no
truncated subtraction and Laplace expansion applies to the square matrix unchanged. The printed
sign `(-1)^(i + 1)` counts rows from one; `(-1)^i` is the same alternation at a zero-based index.

## Inputs
* `H` – matrix holding the given vectors as columns

## Output
* the vector of alternating minors, orthogonal to the columns

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes".
      arXiv, 2015.
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Def. 2]: the alternating minors of `H`, one row dropped at a time. -/
def nCross (H : Mat ℝ (n + 1) n) : Vec ℝ (n + 1) :=
  fun i => (-1) ^ (i : ℕ) * (H.submatrix i.succAbove id).det


/-- Pairing with `nX(H)` is the determinant of `H` with that vector prepended as
a column — Laplace expansion along column zero, read backwards. -/
theorem dotProduct_nCross (H : Mat ℝ (n + 1) n) (v : Vec ℝ (n + 1)) : -- --- CONCL ---
    v ⬝ᵥ nCross H = (Matrix.of fun i => Fin.cons (v i) (H i)).det := by -- --- PROOF ---
  rw [Matrix.det_succ_column_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hsub : (Matrix.of fun i => Fin.cons (v i) (H i)).submatrix i.succAbove Fin.succ
      = H.submatrix i.succAbove id := by
    ext a b
    simp [Matrix.submatrix]
  rw [hsub]
  simp only [nCross, Matrix.of_apply, Fin.cons_zero]
  ring

/-- What makes `nX(H)` a normal vector: it annihilates every column of `H`,
the prepended column then repeating one already there. -/
theorem nCross_dotProduct_col (H : Mat ℝ (n + 1) n) (j : Fin n) :
    (fun i => H i j) ⬝ᵥ nCross H = 0 := by
  rw [dotProduct_nCross]
  refine Matrix.det_zero_of_column_eq (Ne.symm (Fin.succ_ne_zero j)) fun k => ?_
  simp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
