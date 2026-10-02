import CORALean.ContSet.Polygon.Float.Operations.OfPieces

/-!
# `Polygon.ofPieces` denotes the union
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.construct_ofPieces (pieces : List (VPolytope 𝕋 2)) :
    ContSet.construct (Polygon.ofPieces pieces) = ⋃ p ∈ pieces, VPolytope.construct p := rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
