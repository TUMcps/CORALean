import CORALean.ContSet.Taylm.Float.Taylm
import CORALean.ContSet.Interval.Float.Operations.MulLo
import CORALean.ContSet.Interval.Float.Operations.MulHi

/-!
# `Taylm.boundsProd`

The product of an interval by a list of intervals, factor by factor through the corner products
rounded outward.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {ι : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.boundsProd (E : ι → 𝕋 × 𝕋) : List ι → 𝕋 × 𝕋 → 𝕋 × 𝕋
  | [], I => I
  | k :: l, I => Taylm.boundsProd E l
    (Interval.mulLo I.1 I.2 (E k).1 (E k).2, Interval.mulHi I.1 I.2 (E k).1 (E k).2)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
