import CORALean.ContSet.PolyZonotope.Float.PolyZonotope
import CORALean.ContSet.PolyZonotope.Real.Operations.FactorIdx
import CORALean.ContSet.PolyZonotope.Real.Operations.UsedFactors

/-!
# Dropping the factors no column reads, over a floating-point scalar

Split out of `Compact.lean` (issue #62): read again by `compact` in this
directory and by `Theorems/CompactFactorsOuter.lean` and
`Theorems/CompactFactorsNominal.lean`, all outside this file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The factors no column reads, dropped. Only `p` and the exponent matrix
change, both over ℕ, so nothing rounds and the box is untouched. -/
def PolyZonotope.compactFactors (PZ : PolyZonotope 𝕋 n) : PolyZonotope 𝕋 n where
  p := (Real.PolyZonotope.usedFactors PZ.E).card
  h := PZ.h
  q := PZ.q
  c := PZ.c
  G := PZ.G
  E := fun k i => PZ.E (Real.PolyZonotope.factorIdx PZ.E k) i
  GI := PZ.GI
  err := PZ.err

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
