module

public import CORALean.ContSet.Interval.Real.Interval
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

/-!
# `Interval.sqrt`

CORA's `@interval/sqrt`: the square root is increasing on `[0, ∞)`, so it acts on the two bounds,
coordinate by coordinate.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Interval.sqrt (I : Interval (Vec ℝ n)) : Interval (Vec ℝ n) where
  inf := fun i => Real.sqrt (I.inf i)
  sup := fun i => Real.sqrt (I.sup i)


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
