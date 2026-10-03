import CORALean.ContSet.Ellipsoid.Float.Ellipsoid
import CORALean.ContSet.Interval.Float.Operations.RepresentsaPoint

/-!
# `Ellipsoid.representsa_point`, over a floating-point scalar

CORA's `@ellipsoid/representsa_` at type `point` with tolerance `0`: every generator is `0`, and the
error box is a single point. `le` answers only `true` reliably, so a `true` here is sound and a
`false` decides nothing.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Ellipsoid.representsa_point (E : Ellipsoid 𝕋 n) : Bool :=
  (((List.finRange E.k).all fun j => (List.finRange n).all fun i =>
    FloatOps.le (E.G i j) zero && FloatOps.le zero (E.G i j)) &&
    E.err.representsa_point)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
