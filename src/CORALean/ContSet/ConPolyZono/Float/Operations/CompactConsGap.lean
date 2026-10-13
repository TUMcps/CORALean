import CORALean.ContSet.ConPolyZono.Float.Operations.MergedConsCol
import CORALean.ContSet.ConPolyZono.Float.Operations.MergedConsColUp

/-!
# `ConPolyZono.compactConsGap`

What a merged constraint column can be off by.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What a merged constraint column can be off by. -/
def ConPolyZono.compactConsGap (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) :
    Mat 𝕋 cPZ.m (PolyZonotope.repKeep cPZ.EC).card :=
  fun i l => subUp (cPZ.mergedConsColUp i l) (cPZ.mergedConsCol i l)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
