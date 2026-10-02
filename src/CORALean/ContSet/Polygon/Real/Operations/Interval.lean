import CORALean.ContSet.Polygon.Real.Operations.IntervalOfList

/-!
# `Polygon.interval`

CORA's `polygon/interval`: the smallest box holding the polygon, here the hull of the pieces'
boxes (`Interval.or`), the empty box for no pieces.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The box holding every piece. -/
noncomputable def Polygon.interval (P : Polygon) : Interval (Vec ℝ 2) :=
  Polygon.intervalOfList P.sets

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
