import CORALean.Global.Tensor
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

/-!
# Descending products of a matrix sequence

CORA's `computeGO_k` multiplies the Jacobians `A_lin{k}, A_lin{k-1}, ...` in that order, one
more factor for each earlier input. `descProd A hi d` is that product of `d` factors, from
`A hi` down: `A hi * A (hi - 1) * ... * A (hi - d + 1)`, and `1` for `d = 0`. Indices are
`0`-based, so CORA's `A_lin{k}` is `A (k - 1)`.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `A hi * A (hi - 1) * ... `, `d` factors. -/
def descProd (A : ℕ → Mat ℝ n n) (hi : ℕ) : ℕ → Mat ℝ n n
  | 0 => 1
  | d + 1 => A hi * descProd A (hi - 1) d

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
