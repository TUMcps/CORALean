module

public import CORALean.ContSet.Conversion.Real.ZonoBundle_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Zonotope_to_Interval
public import Mathlib.Order.BourbakiWitt

@[expose] public section

/-!
# A bundle's box, at one component — the construction

`ZonoBundle.interval` is the construction; `ZonoBundle_to_Interval` states and proves what it
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

def ZonoBundle.interval (zB : ZonoBundle (Vec ℝ n)) (i : Fin zB.k) : Interval (Vec ℝ n) :=
  (zB.zonotope i).interval

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
