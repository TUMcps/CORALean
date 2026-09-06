import CORALean.ContSet.PolyZonotope.Float.Operations.FiberUp
import CORALean.ContSet.PolyZonotope.Float.Operations.KeepIdx

/-!
# The merged column rounded the other way

Split out of `Compact.lean` (issue #62): read again by `compactGap` in this
directory and by `Theorems/CompactGensOuter.lean`, both outside this file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The same fibre rounded the other way, which is what bounds the gap. -/
def PolyZonotope.mergedColUp (PZ : PolyZonotope 𝕋 n) (i : Fin n)
    (j : Fin (PolyZonotope.repKeep PZ.E).card) : 𝕋 :=
  PolyZonotope.fiberUp (Real.PolyZonotope.rep PZ.E) PZ.G i (PolyZonotope.keepIdx PZ.E j)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
