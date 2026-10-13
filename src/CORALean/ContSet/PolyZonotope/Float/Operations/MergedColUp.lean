import CORALean.ContSet.PolyZonotope.Float.Operations.FiberUp
import CORALean.ContSet.PolyZonotope.Float.Operations.KeepIdx

/-!
# The merged column rounded the other way

Split out of `Compact.lean` (issue #62): read again by `compactGap` in this
directory and by `Theorems/CompactGensOuter.lean`, both outside this file.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The same fibre rounded the other way, which is what bounds the gap. -/
def PolyZonotope.mergedColUp (pZ : PolyZonotope (Vec 𝕋 n)) (i : Fin n)
    (j : Fin (PolyZonotope.repKeep pZ.E).card) : 𝕋 :=
  PolyZonotope.fiberUp (Real.PolyZonotope.rep pZ.E) (fun i l => pZ.G l i) i
    (PolyZonotope.keepIdx pZ.E j)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
