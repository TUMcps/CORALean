module

public import CORALean.ContSet.Interval.Real.Interval

@[expose] public section

/-!
# `Interval.diagVec`

CORA's `@interval/diag` on a matrix: `interval(diag(I.inf), diag(I.sup))`, the diagonal read
off as a vector box. MATLAB's `diag` builds a matrix from a vector and reads the diagonal of a
matrix, so the two are `diag` and `diagVec` here.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A matrix box as the box of its diagonals. -/
def Interval.diagVec (I : Interval (Mat ℝ n n)) : Interval (Vec ℝ n) where
  inf := fun i => I.inf i i
  sup := fun i => I.sup i i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
