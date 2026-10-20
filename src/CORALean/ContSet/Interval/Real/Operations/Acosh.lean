module

public import CORALean.ContSet.Interval.Real.Interval
public import Mathlib.Analysis.SpecialFunctions.Arcosh

@[expose] public section

/-!
# `Interval.acosh`

CORA's `@interval/acosh`:
the inverse hyperbolic cosine is increasing for `1 ≤ x`, so it acts on the two
bounds, coordinate by coordinate.

## Inputs
* `I` – interval box

## Output
* box of the inverse hyperbolic cosines of the bounds
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Interval.acosh (I : Interval (Vec ℝ n)) : Interval (Vec ℝ n) where
  inf := fun i => Real.arcosh (I.inf i)
  sup := fun i => Real.arcosh (I.sup i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
