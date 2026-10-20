module

public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# `Polygon.intervalOfList`

The hull of a list of pieces' boxes (`Interval.or`), the empty box for none.

## Inputs
* none

## Output
* the hull of a list of pieces' boxes
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The hull of a list of pieces' boxes. -/
noncomputable def Polygon.intervalOfList : List (VPolytope (Vec ℝ 2)) → Interval (Vec ℝ 2)
  | [] => Interval.empty 2
  | [p] => VPolytope.interval p
  | p :: q :: ps => (VPolytope.interval p).or (Polygon.intervalOfList (q :: ps))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
