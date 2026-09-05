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

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- What a merged constraint column can be off by. -/
def ConPolyZono.compactConsGap (C : ConPolyZono 𝕋 n) :
    Mat 𝕋 C.m (PolyZonotope.repKeep C.EC).card :=
  fun i l => subUp (C.mergedConsColUp i l) (C.mergedConsCol i l)

end CORALean.Float
