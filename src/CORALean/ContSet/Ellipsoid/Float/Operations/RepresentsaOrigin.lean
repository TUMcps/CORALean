module

public import CORALean.ContSet.Ellipsoid.Float.Operations.RepresentsaPoint
public import CORALean.ContSet.Interval.Float.Operations.Basic

@[expose] public section

/-!
# `Ellipsoid.representsa_origin`, over a floating-point scalar

CORA's `@ellipsoid/representsa_` at type `origin` with tolerance `0`: the shape matrix and the
center are `0`, and the error box is `{0}`. A `true` is sound, a `false` decides nothing.
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Ellipsoid.representsa_origin (E : Ellipsoid 𝕋 n) : Bool :=
  (((List.finRange n).all fun i => (List.finRange n).all fun j =>
    FloatOps.le (E.Q i j) zero && FloatOps.le zero (E.Q i j)) &&
    (List.finRange n).all (fun i => FloatOps.le (E.q i) zero && FloatOps.le zero (E.q i)) &&
    E.I_error.representsa_origin)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
