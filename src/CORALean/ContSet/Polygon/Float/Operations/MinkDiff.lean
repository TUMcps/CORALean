import CORALean.ContSet.HPolytope.Float.Operations.MinkDiffOf
import CORALean.ContSet.Polygon.Float.Operations.BoundDot
import CORALean.ContSet.Polygon.Float.Operations.InnerHRep

/-!
# `Polygon.minkDiff`

CORA's `polygon/minkDiff(pgon, subtrahend)` over a floating-point scalar, by a different
route from CORA's sweep (`Polygon.minkDiff` of the exact layer): every minuend piece with a
certified inner halfspace description (`Polygon.innerHRep`; a piece without one is dropped)
has each of its rows shifted inward by a float upper bound of the subtrahend's support in that
row's direction (`Polygon.boundDot`, at the stored row, which is the exact normal), the shift
rounded so the bound only shrinks (`HPolytope.minkDiffOf`). A halfspace minus any set is the
halfspace shifted by the set's support, so the subtrahend need not be convex, and no boundary
loop is read. The result is the union of these halfspace pieces: inside the Minkowski
difference of the two regions, not equal to it, since a point whose translate of the
subtrahend straddles two minuend pieces is never found, and nor is anything of a dropped
piece.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Each certified minuend piece, its edge rows shifted inward by the subtrahend's support. -/
def Polygon.minkDiff (P Q : Polygon 𝕋) : SetUnion (HPolytope 𝕋 2) :=
  ⟨P.sets.filterMap fun p => (Polygon.innerHRep p).map fun H =>
    H.minkDiffOf (ContSet.construct Q) fun i => Q.boundDot (H.A i) fun _ => rfl⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
