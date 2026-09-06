import CORALean.ContSet.ConPolyZono.Real.ConPolyZono
import CORALean.ContSet.PolyZonotope.Real.Operations.Compact

/-!
# `ConPolyZono.compactGens`

Equal exponent columns added together and the zero generators gone. The whole
constraint block stands, `p` included, so the constraint is untouched.
Noncomputable for that reason: dropping a zero column decides whether an
element of an arbitrary real module is zero.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Equal exponent columns added together and the zero generators gone. The
whole constraint block stands, `p` included, so the constraint is untouched. -/
noncomputable def ConPolyZono.compactGens (C : ConPolyZono α) : ConPolyZono α where
  p := C.p
  h := (PolyZonotope.compactKeep C.E C.G).card
  q := C.q
  m := C.m
  s := C.s
  c := C.c
  G := fun j => PolyZonotope.fiberSum (PolyZonotope.rep C.E) C.G
                  (PolyZonotope.compactIdx C.E C.G j)
  E := fun k j => C.E k (PolyZonotope.compactIdx C.E C.G j)
  GI := C.GI
  A := C.A
  b := C.b
  EC := C.EC

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
