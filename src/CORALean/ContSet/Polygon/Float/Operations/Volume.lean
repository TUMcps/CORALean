module

public import CORALean.ContSet.Polygon.Float.Operations.Interval
public import CORALean.ContSet.Interval.Float.Operations.Volume

@[expose] public section

/-!
# `Polygon.volume`, over a floating-point scalar

An upper bound on CORA's `@polygon/volume_` (the area of the region): the area of the float
interval hull of the polygon, every width and the product rounded up. Not the area: CORA reads
it off the polyshape boundary (R-PG), and the real layer bounds it by the sum of the piece
areas; this bound is coarser still.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def Polygon.volume (P : Polygon 𝕋) : 𝕋 := Interval.volume (Polygon.interval P)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
