import CORALean.ContSet.Interval.Float.Operations.Radius
import CORALean.Global.Float.EuclideanNorm

/-!
# `Interval.radiusSq` over floats

CORA's `radius`, the squared Euclidean norm of the stored half-widths `Interval.radius`, rounded up.
The root is a caller's certificate, as for `Interval.normSq`.
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

def Interval.radiusSq (I : Interval (Vec 𝕋 n)) : 𝕋 := sqSumUp I.radius

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
