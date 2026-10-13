import CORALean.ContSet.Polygon.Real.Polygon
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# `Polygon.volume`

CORA's `polygon/volume_` is the area of the polyshape. The region's area is the Lebesgue measure
of what the pieces denote, bounded and (for null-overlapping pieces) given by the sum of the
pieces' areas `Polygon.pieceAreas`. No formula (shoelace) for a piece's area is given.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The area of the region: Lebesgue measure of the union of the pieces. -/
noncomputable def Polygon.volume (P : Polygon) : ENNReal :=
  MeasureTheory.volume (ContSet.construct P)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
