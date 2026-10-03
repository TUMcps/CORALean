import CORALean.ContSet.Ellipsoid.Float.Operations.RepresentsaPoint
import CORALean.ContSet.Interval.Float.Operations.RepresentsaOrigin

/-!
# `Ellipsoid.representsa_origin`, over a floating-point scalar

CORA's `@ellipsoid/representsa_` at type `origin` with tolerance `0`: every generator and the
centre are `0`, and the error box is `{0}`. A `true` is sound, a `false` decides nothing.
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

def Ellipsoid.representsa_origin (E : Ellipsoid 𝕋 n) : Bool :=
  (((List.finRange E.k).all fun j => (List.finRange n).all fun i =>
    FloatOps.le (E.G i j) zero && FloatOps.le zero (E.G i j)) &&
    (List.finRange n).all (fun i => FloatOps.le (E.q i) zero && FloatOps.le zero (E.q i)) &&
    E.err.representsa_origin)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
