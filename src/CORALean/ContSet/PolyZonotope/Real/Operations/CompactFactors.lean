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


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The factors no column reads, dropped. Only `p` changes; every generator and
every column stands. -/
def PolyZonotope.compactFactors (pZ : PolyZonotope α) : PolyZonotope α where
  p := (PolyZonotope.usedFactors pZ.E).card
  h := pZ.h
  q := pZ.q
  c := pZ.c
  G := pZ.G
  E := fun k i => pZ.E (PolyZonotope.factorIdx pZ.E k) i
  GI := pZ.GI

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
