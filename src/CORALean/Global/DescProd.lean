module

public import CORALean.Global.Tensor
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# Descending products of a matrix sequence

CORA's `computeGO_k` multiplies the Jacobians `A_lin{k}, A_lin{k-1}, ...` in that order, one
more factor for each earlier input. `descProd A hi d` is that product of `d` factors, from
`A hi` down: `A hi * A (hi - 1) * ... * A (hi - d + 1)`, and `1` for `d = 0`. Indices are
`0`-based, so CORA's `A_lin{k}` is `A (k - 1)`.

## Inputs
* `A` – matrix sequence
* `hi` – index of the first factor

## Output
* the function giving the product of the first `d` factors, descending from the index
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


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
