import CORALean.ContSet.Polygon.Float.Operations.Plus

/-!
# `Polygon.plus` encloses the Minkowski sum

By `SetUnion.plus_outer` at the float polytope's `plus`, whose rounding is in its error box.
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

theorem Polygon.plus_outer (P Q : Polygon 𝕋) :
    ContSet.construct P + ContSet.construct Q ⊆ ContSet.construct (Polygon.plus P Q) :=
  SetUnion.plus_outer P Q

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
