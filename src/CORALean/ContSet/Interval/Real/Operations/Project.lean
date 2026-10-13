import CORALean.ContSet.Interval.Real.Interval

/-!
# `Interval.project`

CORA's `@interval/project`: the bounds at the chosen coordinates, in the chosen order, which may
repeat.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.project (I : Interval (Vec ℝ n)) (dims : Fin m → Fin n) : Interval (Vec ℝ m) where
  inf := fun k => I.inf (dims k)
  sup := fun k => I.sup (dims k)


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
