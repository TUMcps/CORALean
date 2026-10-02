import CORALean.ContSet.Interval.Float.Operations.Center
import CORALean.ContSet.Interval.Float.Operations.CenterLo

/-!
# `Interval.centerBox` over floats

The two roundings of the midpoint as a box, which holds the real midpoint (`Theorems/CenterOuter`).
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

def Interval.centerBox (I : Interval (Vec 𝕋 n)) : Interval (Vec 𝕋 n) := ⟨I.centerLo, I.center⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
