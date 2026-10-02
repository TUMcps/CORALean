import CORALean.ContSet.Polygon.Real.Operations.OfPieces

/-!
# `Polygon.ofPieces` denotes the union

The constructor's denotation: the union of the pieces' vertex hulls.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.construct_ofPieces (pieces : List (VPolytope (Vec ℝ 2))) :
    ContSet.construct (Polygon.ofPieces pieces) = ⋃ p ∈ pieces, VPolytope.construct p := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
