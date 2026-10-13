module

public import CORALean.ContSet.Interval.Real.Interval

@[expose] public section

/-!
# `Interval.transpose`

CORA's `@interval/transpose`: transpose both bound matrices.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.transpose (I : Interval (Mat ℝ m n)) : Interval (Mat ℝ n m) where
  inf := I.inf.transpose
  sup := I.sup.transpose

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
