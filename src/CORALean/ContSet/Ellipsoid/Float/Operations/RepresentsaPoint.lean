module

public import CORALean.ContSet.Ellipsoid.Float.Ellipsoid
public import CORALean.ContSet.Interval.Float.Operations.Basic

@[expose] public section

/-!
# `Ellipsoid.representsa_point`, over a floating-point scalar

CORA's `@ellipsoid/representsa_` at type `point` with tolerance `0`: the shape matrix is `0`, and
the error box is a single point. `le` answers only `true` reliably, so a `true` here is sound and a
`false` decides nothing.
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

def Ellipsoid.representsa_point (E : Ellipsoid 𝕋 n) : Bool :=
  (((List.finRange n).all fun i => (List.finRange n).all fun j =>
    FloatOps.le (E.Q i j) zero && FloatOps.le zero (E.Q i j)) &&
    E.I_error.representsa_point)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
