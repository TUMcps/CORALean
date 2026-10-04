import CORALean.Global.Tensor
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin

/-!
# Selecting a block of a stacked vector

CORA's `[eye(nx) zeros(nx, ny)]` and `[zeros(ny, nx) eye(ny)]` of `computeGO_k`: the
matrices that pick the first `nx` and the last `ny` entries of a stacked vector `L = [L_x; L_y]`.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


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
