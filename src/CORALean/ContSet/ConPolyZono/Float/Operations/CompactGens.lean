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
def ConPolyZono.compactGens (cPZ : ConPolyZono 𝕋 n) : ConPolyZono 𝕋 n where
  p := cPZ.p
  h := (PolyZonotope.repKeep cPZ.E).card
  q := cPZ.q
  m := cPZ.m
  s := cPZ.s
  c := cPZ.c
  G := cPZ.mergedCol
  E := fun k j => cPZ.E k (PolyZonotope.keepIdx cPZ.E j)
  GI := cPZ.GI
  A := cPZ.A
  b := cPZ.b
  EC := cPZ.EC
  err := cPZ.err.plus (PolyZonotope.generatorError (ConPolyZono.compactGensGap cPZ))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
