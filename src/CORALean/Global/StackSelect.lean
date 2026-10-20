module

public import CORALean.Global.Tensor
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# Selecting a block of a stacked vector

CORA's `[eye(nx) zeros(nx, ny)]` and `[zeros(ny, nx) eye(ny)]` of `computeGO_k`: the
matrices that pick the first `nx` and the last `ny` entries of a stacked vector `L = [L_x; L_y]`.

## Inputs
* `n` – length of the first block
* `r` – length of the second block

## Output
* the matrix picking the first block of a stacked vector
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n r : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `[eye(n) zeros(n, r)]`. -/
def stackFst (n r : ℕ) : Mat ℝ n (n + r) := Matrix.of fun i j => if j.val = i.val then 1 else 0

/-- `[zeros(r, n) eye(r)]`. -/
def stackSnd (n r : ℕ) : Mat ℝ r (n + r) :=
  Matrix.of fun i j => if j.val = n + i.val then 1 else 0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
