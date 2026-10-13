import CORALean.ContSet.ConPolyZono.Float.Operations.CompactGensGap
import CORALean.ContSet.Interval.Float.Operations.Plus
import CORALean.ContSet.PolyZonotope.Float.Operations.GeneratorError

/-!
# `ConPolyZono.compactGensSpec`

Equal exponent columns added together, the stored value the lower rounding
and the gap paid into the ambient box. The constraint block stands.

The definition `compactGens` is proved equal to, which computes the same thing
from tables built once (issue #61). This one is the statement the soundness proof
reads: every entry a named, separately provable lookup.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The specification of `compactGens`: equal exponent columns added together, the
stored value the lower rounding and the gap paid into the ambient box. The
constraint block stands. -/
def ConPolyZono.compactGensSpec (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) : ConPolyZono 𝕋 (Vec 𝕋 n) where
  p := cPZ.p
  h := (PolyZonotope.repKeep cPZ.E).card
  q := cPZ.q
  m := cPZ.m
  s := cPZ.s
  c := cPZ.c
  G := fun j i => cPZ.mergedCol i j
  E := fun k j => cPZ.E k (PolyZonotope.keepIdx cPZ.E j)
  GI := cPZ.GI
  A := cPZ.A
  b := cPZ.b
  EC := cPZ.EC
  err := cPZ.err.plus (PolyZonotope.generatorError (ConPolyZono.compactGensGap cPZ))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
