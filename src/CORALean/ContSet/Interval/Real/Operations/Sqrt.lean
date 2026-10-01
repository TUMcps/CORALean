import CORALean.ContSet.Interval.Real.Interval

/-!
# `Interval.sqrt`

CORA's `@interval/sqrt`: the square root is increasing on `[0, ∞)`, so it acts on the two bounds,
coordinate by coordinate.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Interval.sqrt (I : Interval (Vec ℝ n)) : Interval (Vec ℝ n) where
  inf := fun i => Real.sqrt (I.inf i)
  sup := fun i => Real.sqrt (I.sup i)


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
