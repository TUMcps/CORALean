module

public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import CORALean.ContSet.Interval.Real.Interval

@[expose] public section

/-!
# `Interval.asinh`

CORA's `@interval/asinh`: the inverse hyperbolic sine is strictly increasing and continuous on all
of `ℝ`, so it acts on the two bounds, coordinate by coordinate.

## Inputs
* `I` – interval box

## Output
* box of the inverse hyperbolic sines of the bounds
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Interval.asinh (I : Interval (Vec ℝ n)) : Interval (Vec ℝ n) where
  inf := fun i => Real.arsinh (I.inf i)
  sup := fun i => Real.arsinh (I.sup i)


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
