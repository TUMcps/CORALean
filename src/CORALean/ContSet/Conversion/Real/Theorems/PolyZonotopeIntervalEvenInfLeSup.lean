module

public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval
public import CORALean.ContSet.PolyZonotope.Real.Theorems.PointMemConstruct
public import Mathlib.Order.BourbakiWitt
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Theorems.PolyZonotopeIntervalEvenContains

@[expose] public section

/-!
# A polynomial zonotope as a box: `intervalEven_inf_le_sup`

## Inputs
* `pZ` – polynomial zonotope
* `i` – coordinate

## Hypotheses
* none

## Conclusion
* lower end of the tighter interval is below its upper end
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   12-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The tighter box is ordered too, the same way `interval`'s is. -/
theorem PolyZonotope.intervalEven_inf_le_sup (pZ : PolyZonotope (Vec ℝ n)) (i : Fin n) :
    pZ.intervalEven.inf i ≤ pZ.intervalEven.sup i := by
  have hmem := pZ.intervalEven_contains (pZ.point_mem_construct (a := fun _ => 0)
    fun _ => by rw [abs_zero]; exact zero_le_one)
  exact le_trans (hmem i).1 (hmem i).2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
