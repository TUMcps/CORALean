import CORALean.ContSet.ConPolyZono.Float.Operations.CompactGensGap
import CORALean.ContSet.Interval.Float.Operations.Plus
import CORALean.ContSet.PolyZonotope.Float.Operations.GeneratorError

/-!
# `ConPolyZono.compactGens`

Equal exponent columns added together, the stored value the lower rounding
and the gap paid into the ambient box. The constraint block stands.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Equal exponent columns added together, the stored value the lower rounding
and the gap paid into the ambient box. The constraint block stands. -/
def ConPolyZono.compactGens (C : ConPolyZono 𝕋 n) : ConPolyZono 𝕋 n where
  p := C.p
  h := (PolyZonotope.repKeep C.E).card
  q := C.q
  m := C.m
  s := C.s
  c := C.c
  G := C.mergedCol
  E := fun k j => C.E k (PolyZonotope.keepIdx C.E j)
  GI := C.GI
  A := C.A
  b := C.b
  EC := C.EC
  err := C.err.plus (PolyZonotope.generatorError (ConPolyZono.compactGensGap C))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
