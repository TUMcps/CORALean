import CORALean.ContSet.Polygon.Real.Operations.OfPieces
import CORALean.ContSet.VPolytope.Real.Instances

/-!
# `Polygon.ofPieces` denotes the union

The constructor's denotation: the union of the pieces' vertex hulls.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.construct_ofPieces (pieces : List (VPolytope (Vec ℝ 2))) :
    ContSet.construct (Polygon.ofPieces pieces) = ⋃ p ∈ pieces, VPolytope.construct p := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
