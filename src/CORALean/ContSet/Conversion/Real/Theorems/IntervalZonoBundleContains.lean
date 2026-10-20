module

public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeZonoBundleExact
public import Mathlib.Order.BourbakiWitt
public import CORALean.ContSet.Conversion.Real.Operations.Basic

@[expose] public section

/-!
# A box as a bundle of one

Through the box's own zonotope, then `Zonotope.zonoBundle` — the single-member
bundle, exact by `Set.iInter_const`. All the loss is the box-to-zonotope step's,
so this is no worse than `Interval → Zonotope` already is.

## Inputs
* `I` – interval

## Hypotheses
* none

## Conclusion
* interval is contained in its zonotope bundle
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.zonoBundle_contains (I : Interval (Vec ℝ n)) :
    I.construct ⊆ I.zonoBundle.construct :=
  subset_trans I.zonotope_contains (Zonotope.zonoBundle_exact _).subset

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
