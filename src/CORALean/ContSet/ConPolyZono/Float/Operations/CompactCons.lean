import CORALean.ContSet.ConPolyZono.Float.Operations.CompactConsB
import CORALean.ContSet.ConPolyZono.Float.Operations.MergedConsCol

/-!
# `ConPolyZono.compactCons`

Equal constraint exponent columns added together, the stored value the lower
rounding and the widening paid into `b`. The generators stand, so the ambient
box is untouched.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- Equal constraint exponent columns added together, the stored value the lower
rounding and the widening paid into `b`. The generators stand, so the ambient
box is untouched. -/
def ConPolyZono.compactCons (C : ConPolyZono 𝕋 n) : ConPolyZono 𝕋 n where
  p := C.p
  h := C.h
  q := C.q
  m := C.m
  s := (PolyZonotope.repKeep C.EC).card
  c := C.c
  G := C.G
  E := C.E
  GI := C.GI
  A := C.mergedConsCol
  b := ConPolyZono.compactConsB C
  EC := fun k l => C.EC k (PolyZonotope.keepIdx C.EC l)
  err := C.err

end CORALean.Float
