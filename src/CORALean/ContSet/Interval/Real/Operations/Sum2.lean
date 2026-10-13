module

public import CORALean.ContSet.Interval.Real.Interval

@[expose] public section

/-!
# `Interval.sum₂`

CORA's `@interval/sum` of an interval matrix along dimension 2: the bounds are summed along each
row, `sum(I.inf, 2)` and `sum(I.sup, 2)`. CORA keeps the result as an `m × 1` matrix; here it is
the vector of the same entries.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.sum₂ (I : Interval (Mat ℝ m n)) : Interval (Vec ℝ m) where
  inf := fun i => ∑ j, I.inf i j
  sup := fun i => ∑ j, I.sup i j

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
