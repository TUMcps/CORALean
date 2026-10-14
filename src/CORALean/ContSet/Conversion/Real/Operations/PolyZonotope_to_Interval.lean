module

public import CORALean.ContSet.Conversion.Real.PolyZonotope_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Zonotope_to_Interval
public import CORALean.ContSet.PolyZonotope.Real.Theorems.PointMemConstruct
public import Mathlib.Order.BourbakiWitt

@[expose] public section

/-!
# A polynomial zonotope as a box — the construction

`PolyZonotope.interval` and `PolyZonotope.intervalEven` are the constructions;
`PolyZonotope_to_Interval` states and proves what they guarantee.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   12-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.interval (pZ : PolyZonotope (Vec ℝ n)) : Interval (Vec ℝ n) :=
  pZ.zonotope.interval

/-- The tighter box, through `zonotopeEven`: an even-exponent generator halves
into the centre instead of being boxed whole. -/
noncomputable def PolyZonotope.intervalEven (pZ : PolyZonotope (Vec ℝ n)) : Interval (Vec ℝ n) :=
  pZ.zonotopeEven.interval

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
