import CORALean.ContSet.Zonotope.Float.Zonotope
import CORALean.ContSet.Interval.Float.Operations.RepresentsaPoint

/-!
# `Zonotope.representsa_point`, over a floating-point scalar

CORA's `@zonotope/representsa_` at type `point` with tolerance `0`: every generator is `0`, and the
error box is a single point. `le` answers only `true` reliably, so a `true` here is sound and a
`false` decides nothing.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.representsa_point (Z : Zonotope (Vec 𝕋 n)) : Bool :=
  (((List.finRange Z.h).all fun j => (List.finRange n).all fun i =>
    FloatOps.le (Z.G j i) zero && FloatOps.le zero (Z.G j i)) &&
    Z.E.representsa_point)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
