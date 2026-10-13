module

public import CORALean.ContSet.Polygon.Float.Operations.PieceHolds

@[expose] public section

/-!
# `Polygon.pieceSubset`

A float piece lies inside another: every stored vertex of the first is in the second's nominal
hull (`Polygon.pieceHolds`), and the first's error box lies in the second's (`le` on the
corners). Sufficient only: a piece covered with the help of the second box's slack is not
recognised.
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

def Polygon.pieceSubset (p q : VPolytope (Vec 𝕋 2)) : Bool :=
  ((List.finRange p.k).all fun l => Polygon.pieceHolds q (p.V l)) &&
    (List.finRange 2).all fun i => le (q.E.inf i) (p.E.inf i) && le (p.E.sup i) (q.E.sup i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
