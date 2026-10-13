module

public import CORALean.ContSet.Interval.Float.Operations.Plus
public import CORALean.ContSet.PolyZonotope.Float.Operations.CompactGap
public import CORALean.ContSet.PolyZonotope.Float.Operations.GeneratorError

@[expose] public section

/-!
# Merging equal-column generators, over a floating-point scalar

Split out of `Compact.lean` (issue #62): read again by `compact` in this
directory and by several `Theorems/` files, all outside this file.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Equal exponent columns added together, the stored value the lower rounding
and the gap paid into the box. The factors are untouched. -/
def PolyZonotope.compactGens (pZ : PolyZonotope (Vec 𝕋 n)) : PolyZonotope (Vec 𝕋 n) where
  p := pZ.p
  h := (PolyZonotope.repKeep pZ.E).card
  q := pZ.q
  c := pZ.c
  G := fun j i => pZ.mergedCol i j
  E := fun k j => pZ.E k (PolyZonotope.keepIdx pZ.E j)
  GI := pZ.GI
  err := pZ.err.plus (PolyZonotope.generatorError (PolyZonotope.compactGap pZ))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
