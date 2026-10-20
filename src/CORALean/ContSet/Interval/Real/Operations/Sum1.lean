module

public import CORALean.ContSet.Interval.Real.Interval

@[expose] public section

/-!
# `Interval.sum₁`

CORA's `@interval/sum` of an interval matrix along dimension 1: the bounds are summed down each
column, `sum(I.inf, 1)` and `sum(I.sup, 1)`. CORA keeps the result as a `1 × n` matrix; here it is
the vector of the same entries.

## Inputs
* `I` – interval matrix

## Output
* box of the column sums
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.sum₁ (I : Interval (Mat ℝ m n)) : Interval (Vec ℝ n) where
  inf := fun j => ∑ i, I.inf i j
  sup := fun j => ∑ i, I.sup i j

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
