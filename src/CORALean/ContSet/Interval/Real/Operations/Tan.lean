module

public import CORALean.ContSet.Interval.Real.Interval
public import Mathlib.Analysis.Complex.Trigonometric

@[expose] public section

/-!
# `Interval.tan`

CORA's `@interval/tan`: the tangent is increasing on `(-π/2, π/2)`, so it acts on the two bounds,
coordinate by coordinate.

## Inputs
* `I` – interval box

## Output
* box of the tangents of the bounds
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Interval.tan (I : Interval (Vec ℝ n)) : Interval (Vec ℝ n) where
  inf := fun i => Real.tan (I.inf i)
  sup := fun i => Real.tan (I.sup i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
