import CORALean.ContSet.Interval.Float.Operations.Plus
import CORALean.ContSet.PolyZonotope.Float.Operations.CompactGap
import CORALean.ContSet.PolyZonotope.Float.Operations.GeneratorError

/-!
# Merging equal-column generators, over a floating-point scalar

Split out of `Compact.lean` (issue #62): read again by `compact` in this
directory and by several `Theorems/` files, all outside this file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Equal exponent columns added together, the stored value the lower rounding
and the gap paid into the box. The factors are untouched. -/
def PolyZonotope.compactGens (PZ : PolyZonotope 𝕋 n) : PolyZonotope 𝕋 n where
  p := PZ.p
  h := (PolyZonotope.repKeep PZ.E).card
  q := PZ.q
  c := PZ.c
  G := PZ.mergedCol
  E := fun k j => PZ.E k (PolyZonotope.keepIdx PZ.E j)
  GI := PZ.GI
  err := PZ.err.plus (PolyZonotope.generatorError (PolyZonotope.compactGap PZ))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
