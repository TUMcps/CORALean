import CORALean.ContSet.Conversion.Float.Ellipsoid_to_Interval
import CORALean.ContSet.Interval.Float.Operations.Volume

/-!
# `Ellipsoid.volume`, over a floating-point scalar

An upper bound on CORA's `@ellipsoid/volume_`, whose `sqrt(det Q)` and `Γ` no float computes:
the volume of the float interval hull (`Ellipsoid.interval`, one proposed half-width per
coordinate, each checked against its row's rounded-up square sum by `le`), widths and product
rounded up. `none` when a half-width fails its check. Not the volume, and coarser than it by up
to the box-to-ellipsoid ratio.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Ellipsoid.volume (E : Ellipsoid 𝕋 n) (s : Vec 𝕋 n) : Option 𝕋 :=
  if (List.finRange n).all fun i => le (sqSumUp fun j => absolute (E.G i j)) (mulDown (s i) (s i))
  then some (Interval.volume (E.interval s)) else none

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
