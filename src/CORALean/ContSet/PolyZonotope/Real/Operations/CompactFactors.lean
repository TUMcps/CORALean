import CORALean.ContSet.PolyZonotope.Real.Operations.FactorIdx

/-!
# Dropping the factors no column reads

Split out of `Compact.lean` (issue #62): read again by the float layer's own
`compactFactors`, outside this file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

/-- The factors no column reads, dropped. Only `p` changes; every generator and
every column stands. -/
def PolyZonotope.compactFactors (PZ : PolyZonotope α) : PolyZonotope α where
  p := (PolyZonotope.usedFactors PZ.E).card
  h := PZ.h
  q := PZ.q
  c := PZ.c
  G := PZ.G
  E := fun k i => PZ.E (PolyZonotope.factorIdx PZ.E k) i
  GI := PZ.GI

end CORALean.Real
