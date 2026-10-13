module

public import CORALean.ContSet.Polygon.Real.Operations.Volume

@[expose] public section

/-!
# `Polygon.pieceAreas`

The sum of the pieces' own areas, which counts overlaps twice. `Polygon.volume_le_pieceAreas` bounds
the area of the region by it, and `Polygon.volume_eq_pieceAreas` makes it exact when the pieces
overlap in null sets only.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The sum of the pieces' own areas. -/
noncomputable def Polygon.pieceAreas (P : Polygon) : ENNReal :=
  (P.sets.map fun p => MeasureTheory.volume (VPolytope.construct p)).sum

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
