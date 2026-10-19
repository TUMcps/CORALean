module

public import CORALean.Global.EuclideanNorm
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.Data.List.MinMax

@[expose] public section

/-!
# Gram–Schmidt, as CORA's `gramSchmidt`

CORA's `gramSchmidt(B)` (`global/functions/matlab/init/gramSchmidt.m`) runs the classical loop
`v = B(:,j) - Σ_{i<j} (Q(:,i)ᵀ B(:,j)) Q(:,i)`, `Q(:,j) = v / ‖v‖₂` over the columns of `B`. That
loop is Mathlib's `gramSchmidtNormed` (`gramSchmidt_def''` is its formula), so `gramSchmidt` reads
the columns into `EuclideanSpace` through `toEuclidean` and the result back. Where a column
depends on the earlier ones MATLAB divides by zero and returns `NaN`; here the column is `0`.

A single column `g` is first completed (`if size(B,2) == 1`): the unit columns follow it, less
the one `max(abs(g))` picks, the first largest `|gᵢ|` (`List.argmax`). The columns are then
independent whenever `g ≠ 0`, and the result is an orthonormal basis whose first vector is
`g / ‖g‖₂` (`gramSchmidtVec_transpose_mul_self`, `gramSchmidtVec_col_zero`). Over ℝ only,
being a square root and a division: a conversion that needs the basis in floats computes its own
and is sound for whichever basis it computed.
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n k m : ℕ}


/-- CORA's `gramSchmidt(B)`: the columns of `B` orthonormalized in order. -/
noncomputable def gramSchmidt (B : Mat ℝ n k) : Mat ℝ n k :=
  fun i j => InnerProductSpace.gramSchmidtNormed ℝ (fun l => toEuclidean fun r => B r l) j i

/-- The column CORA's completion drops: the first largest `|gᵢ|`. -/
noncomputable def gramSchmidtPivot (g : Vec ℝ (m + 1)) : Fin (m + 1) :=
  ((List.finRange (m + 1)).argmax fun i => |g i|).getD 0


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `gramSchmidt(g)` at one column: `g`, then the unit columns but the pivot's. -/
noncomputable def gramSchmidtVec (g : Vec ℝ (m + 1)) : Mat ℝ (m + 1) (m + 1) :=
  let e : Fin m → Vec ℝ (m + 1) := fun l => Pi.single ((gramSchmidtPivot g).succAbove l) 1
  gramSchmidt (Matrix.of fun i j => Fin.cases (g i) (fun l => e l i) j)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
