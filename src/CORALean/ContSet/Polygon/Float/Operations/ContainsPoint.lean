module

public import CORALean.ContSet.Polygon.Float.Operations.PieceHolds
public import CORALean.ContSet.Polygon.Float.Polygon

@[expose] public section

/-!
# `Polygon.containsPoint`, over a floating-point scalar

CORA's `@polygon/contains_` for a point, at the region: some piece whose error box holds the
origin (`le` both ways) and whose stored vertices hold the point in one of their triangles
(`Polygon.pieceHolds`). No linear program and no certificate. Only `true` is certain; CORA's
tolerance and boundary expansion are not modelled.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def Polygon.containsPoint (P : Polygon 𝕋) (x : Vec 𝕋 2) : Bool :=
  P.sets.any fun p =>
    ((List.finRange 2).all fun i => le (p.I_error.inf i) zero && le zero (p.I_error.sup i)) &&
      Polygon.pieceHolds p x

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
