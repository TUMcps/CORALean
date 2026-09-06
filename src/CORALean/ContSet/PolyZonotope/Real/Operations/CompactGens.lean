import CORALean.ContSet.PolyZonotope.Real.Operations.CompactIdx
import CORALean.ContSet.PolyZonotope.Real.Operations.FiberSum
import CORALean.ContSet.PolyZonotope.Real.Operations.Rep

/-!
# Merging equal-column generators and dropping the zero ones

Split out of `Compact.lean` (issue #62): read again by the float layer's own
`compactGens`, outside this file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

/-- Equal exponent columns added together, and the zero generators gone. The
factors are untouched, so a factor vector carries over unchanged. -/
noncomputable def PolyZonotope.compactGens (PZ : PolyZonotope α) : PolyZonotope α where
  p := PZ.p
  h := (PolyZonotope.compactKeep PZ.E PZ.G).card
  q := PZ.q
  c := PZ.c
  G := fun j => PolyZonotope.fiberSum (PolyZonotope.rep PZ.E) PZ.G
                  (PolyZonotope.compactIdx PZ.E PZ.G j)
  E := fun k j => PZ.E k (PolyZonotope.compactIdx PZ.E PZ.G j)
  GI := PZ.GI

end CORALean.Real
