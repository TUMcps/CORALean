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


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Equal exponent columns added together, and the zero generators gone. The
factors are untouched, so a factor vector carries over unchanged. -/
noncomputable def PolyZonotope.compactGens (pZ : PolyZonotope α) : PolyZonotope α where
  p := pZ.p
  h := (PolyZonotope.compactKeep pZ.E pZ.G).card
  q := pZ.q
  c := pZ.c
  G := fun j => PolyZonotope.fiberSum (PolyZonotope.rep pZ.E) pZ.G
                  (PolyZonotope.compactIdx pZ.E pZ.G j)
  E := fun k j => pZ.E k (PolyZonotope.compactIdx pZ.E pZ.G j)
  GI := pZ.GI

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
