import CORALean.ContSet.PolyZonotope.Float.Operations.FiberDown
import CORALean.ContSet.PolyZonotope.Float.Operations.KeepIdx

/-!
# The merged column, as stored

Split out of `Compact.lean` (issue #62): read again by `compactGap` and
`compactGens` in this directory and by `Theorems/CompactGensOuter.lean`, all
outside this file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The merged column as stored: the lower of the two directed fibre sums. -/
def PolyZonotope.mergedCol (PZ : PolyZonotope 𝕋 n) (i : Fin n)
    (j : Fin (PolyZonotope.repKeep PZ.E).card) : 𝕋 :=
  PolyZonotope.fiberDown (Real.PolyZonotope.rep PZ.E) PZ.G i (PolyZonotope.keepIdx PZ.E j)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
