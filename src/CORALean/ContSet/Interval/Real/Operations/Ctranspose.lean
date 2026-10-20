module

public import CORALean.ContSet.Interval.Real.Operations.Basic

@[expose] public section

/-!
# `Interval.ctranspose`

CORA's `@interval/ctranspose`: the conjugate transpose, which over ℝ is the transpose, and CORA's
code for it is the same line.

## Inputs
* `I` – interval matrix

## Output
* transposed interval matrix
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.ctranspose (I : Interval (Mat ℝ m n)) : Interval (Mat ℝ n m) := I.transpose

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
