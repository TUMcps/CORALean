module

public import CORALean.ContSet.Polygon.Float.Operations.OfPieces

@[expose] public section

/-!
# `Polygon.ofPieces` denotes the union
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.construct_ofPieces (pieces : List (VPolytope (Vec 𝕋 2))) :
    ContSet.construct (Polygon.ofPieces pieces) = ⋃ p ∈ pieces, VPolytope.construct p := rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
