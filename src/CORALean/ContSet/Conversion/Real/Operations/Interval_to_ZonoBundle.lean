module

public import CORALean.ContSet.Conversion.Real.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Zonotope_to_ZonoBundle
public import Mathlib.Order.BourbakiWitt

@[expose] public section

/-!
# A box as a bundle of one — the construction

`Interval.zonoBundle` is the construction; `Interval_to_ZonoBundle` states and proves what it
guarantees.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Interval.zonoBundle (I : Interval (Vec ℝ n)) : ZonoBundle (Vec ℝ n) :=
  I.zonotope.zonoBundle

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
