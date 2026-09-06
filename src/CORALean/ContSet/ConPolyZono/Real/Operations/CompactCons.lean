import CORALean.ContSet.ConPolyZono.Real.Operations.ConsCol
import CORALean.ContSet.PolyZonotope.Real.Operations.Compact

/-!
# `ConPolyZono.compactCons`

Equal constraint exponent columns added together and the zero columns gone.
`b` stands: a merged column is exact, and a column at exponent zero stays a
column here rather than moving into the bound.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Equal constraint exponent columns added together and the zero columns gone.
`b` stands: a merged column is exact, and a column at exponent zero stays a
column here rather than moving into the bound. -/
noncomputable def ConPolyZono.compactCons (C : ConPolyZono α) : ConPolyZono α where
  p := C.p
  h := C.h
  q := C.q
  m := C.m
  s := (PolyZonotope.compactKeep C.EC (ConPolyZono.consCol C.A)).card
  c := C.c
  G := C.G
  E := C.E
  GI := C.GI
  A := fun i l => PolyZonotope.fiberSum (PolyZonotope.rep C.EC) (ConPolyZono.consCol C.A)
                    (PolyZonotope.compactIdx C.EC (ConPolyZono.consCol C.A) l) i
  b := C.b
  EC := fun k l => C.EC k (PolyZonotope.compactIdx C.EC (ConPolyZono.consCol C.A) l)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
