module

public import CORALean.ContSet.Zonotope.Float.Operations.RepresentsaPoint
public import CORALean.ContSet.Interval.Float.Operations.Basic

@[expose] public section

/-!
# `Zonotope.representsa_origin`, over a floating-point scalar

CORA's `@zonotope/representsa_` at type `origin` with tolerance `0`: every generator and the
centre are `0`, and the error box is `{0}`. A `true` is sound, a `false` decides nothing.
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

def Zonotope.representsa_origin (Z : Zonotope (Vec 𝕋 n)) : Bool :=
  (((List.finRange Z.h).all fun j => (List.finRange n).all fun i =>
    FloatOps.le (Z.G j i) zero && FloatOps.le zero (Z.G j i)) &&
    (List.finRange n).all (fun i => FloatOps.le (Z.c i) zero && FloatOps.le zero (Z.c i)) &&
    Z.E.representsa_origin)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
