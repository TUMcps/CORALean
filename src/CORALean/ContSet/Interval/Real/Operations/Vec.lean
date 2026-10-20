module

public import CORALean.ContSet.Interval.Real.Interval
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

/-!
# `Interval.vec`

The reshape `reshape(interval(intMat), [], 1)` that `intervalMatrix` methods (`representsa`,
`volume`, `vertices`) use to reuse the vector interval: the entries stacked column by column,
MATLAB's order. Entry `(i, j)` of an `m × n` matrix is entry `i + m * j` of the vector.

## Inputs
* `A` – interval matrix

## Output
* box of the entries read column by column
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The column-major vectorisation of the bounds: entry `(i, j)` goes to position `i + m * j`. -/
def Interval.vec (A : Interval (Mat ℝ m n)) : Interval (Vec ℝ (n * m)) where
  inf := fun k => A.inf (finProdFinEquiv.symm k).2 (finProdFinEquiv.symm k).1
  sup := fun k => A.sup (finProdFinEquiv.symm k).2 (finProdFinEquiv.symm k).1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
