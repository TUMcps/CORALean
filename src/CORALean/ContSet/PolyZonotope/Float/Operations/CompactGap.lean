import CORALean.ContSet.PolyZonotope.Float.Operations.MergedCol
import CORALean.ContSet.PolyZonotope.Float.Operations.MergedColUp

/-!
# What a merged column can be off by

Split out of `Compact.lean` (issue #62): read again by
`Theorems/CompactGensOuter.lean`, outside this file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What a merged column can be off by. -/
def PolyZonotope.compactGap (pZ : PolyZonotope (Vec 𝕋 n)) :
    Mat 𝕋 n (PolyZonotope.repKeep pZ.E).card :=
  fun i j => subUp (pZ.mergedColUp i j) (pZ.mergedCol i j)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
