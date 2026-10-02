import CORALean.ContSet.Polygon.Real.Polygon
import CORALean.ContSet.Conversion.Real.VPolytope_to_Interval
import CORALean.ContSet.Interval.Real.Operations.Or
import CORALean.ContSet.Interval.Real.Operations.Empty

/-!
# `Polygon.intervalOfList`

The hull of a list of pieces' boxes (`Interval.or`), the empty box for none.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


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
