import CORALean.ContSet.Interval.Real.Operations.Transpose

/-!
# `Interval.ctranspose`

CORA's `@interval/ctranspose`: the conjugate transpose, which over ℝ is the transpose, and CORA's
code for it is the same line.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.ctranspose (I : Interval (Mat ℝ m n)) : Interval (Mat ℝ n m) := I.transpose

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
