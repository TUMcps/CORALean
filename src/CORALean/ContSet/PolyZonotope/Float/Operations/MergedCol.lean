module

public import CORALean.ContSet.PolyZonotope.Float.Operations.FiberDown
public import CORALean.ContSet.PolyZonotope.Float.Operations.KeepIdx

@[expose] public section

/-!
# The merged column, as stored

Split out of `Compact.lean` (issue #62): read again by `compactGap` and
`compactGens` in this directory and by `Theorems/CompactGensOuter.lean`, all
outside this file.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The merged column as stored: the lower of the two directed fibre sums. -/
def PolyZonotope.mergedCol (pZ : PolyZonotope (Vec 𝕋 n)) (i : Fin n)
    (j : Fin (PolyZonotope.repKeep pZ.E).card) : 𝕋 :=
  PolyZonotope.fiberDown (Real.PolyZonotope.rep pZ.E) (fun i l => pZ.G l i) i
    (PolyZonotope.keepIdx pZ.E j)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
