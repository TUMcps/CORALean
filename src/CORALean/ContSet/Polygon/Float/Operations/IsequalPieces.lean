module

public import CORALean.ContSet.Polygon.Float.Operations.PieceSubset
public import CORALean.ContSet.Polygon.Float.Polygon

@[expose] public section

/-!
# `Polygon.isequalPieces`, over a floating-point scalar

The real layer's one-sided `isequal`, as a test: every piece of each polygon lies inside one
piece of the other, each inclusion certified by `Polygon.pieceSubset`. `true` proves the regions
equal; `false` says nothing (a piece may be covered by several pieces, or by one only up to
rounding). CORA's comparison of boundary vertex lists (R-PG) is not what is tested.

## Inputs
* `P` – polygon
* `Q` – polygon

## Output
* `true` when every piece of each polygon lies inside a piece of the other
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def Polygon.isequalPieces (P Q : Polygon 𝕋) : Bool :=
  (P.sets.all fun p => Q.sets.any fun q => Polygon.pieceSubset p q) &&
    Q.sets.all fun q => P.sets.any fun p => Polygon.pieceSubset q p

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
