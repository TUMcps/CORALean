import CORALean.ContSet.Polygon.Real.Operations.Volume

/-!
# `Polygon.pieceAreas`

The sum of the pieces' own areas, which counts overlaps twice. `Polygon.volume_le_pieceAreas` bounds
the area of the region by it, and `Polygon.volume_eq_pieceAreas` makes it exact when the pieces
overlap in null sets only.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The sum of the pieces' own areas. -/
noncomputable def Polygon.pieceAreas (P : Polygon) : ENNReal :=
  (P.sets.map fun p => MeasureTheory.volume (VPolytope.construct p)).sum

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
