import CORALean.ContSet.ConPolyZono.Float.Operations.MergedCol
import CORALean.ContSet.ConPolyZono.Float.Operations.MergedColUp

/-!
# `ConPolyZono.compactGensGap`

What a merged generator column can be off by.
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

/-- What a merged generator column can be off by. -/
def ConPolyZono.compactGensGap (C : ConPolyZono 𝕋 n) :
    Mat 𝕋 n (PolyZonotope.repKeep C.E).card :=
  fun i j => subUp (C.mergedColUp i j) (C.mergedCol i j)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
