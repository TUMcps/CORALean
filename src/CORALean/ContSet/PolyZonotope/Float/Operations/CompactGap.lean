module

public import CORALean.ContSet.PolyZonotope.Float.Operations.MergedCol
public import CORALean.ContSet.PolyZonotope.Float.Operations.MergedColUp

@[expose] public section

/-!
# What a merged column can be off by

Split out of `Compact.lean` (issue #62): read again by
`Theorems/CompactGensOuter.lean`, outside this file.

## Inputs
* `pZ` – polynomial zonotope

## Output
* matrix of the gaps between rounded-up and rounded-down merged columns
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


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
