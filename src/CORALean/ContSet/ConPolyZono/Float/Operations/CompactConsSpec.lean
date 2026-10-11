import CORALean.ContSet.ConPolyZono.Float.Operations.CompactConsB
import CORALean.ContSet.ConPolyZono.Float.Operations.MergedConsCol

/-!
# `ConPolyZono.compactConsSpec`

Equal constraint exponent columns added together, the stored value the lower
rounding and the widening paid into `b`. The generators stand, so the ambient
box is untouched.

The definition `compactCons` is proved equal to, which computes the same thing
from tables built once (issue #61). This one is the statement the soundness proof
reads: every entry a named, separately provable lookup.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The specification of `compactCons`: equal constraint exponent columns added
together, the stored value the lower rounding and the widening paid into `b`.
The generators stand, so the ambient box is untouched. -/
def ConPolyZono.compactConsSpec (cPZ : ConPolyZono 𝕋 n) : ConPolyZono 𝕋 n where
  p := cPZ.p
  h := cPZ.h
  q := cPZ.q
  m := cPZ.m
  s := (PolyZonotope.repKeep cPZ.EC).card
  c := cPZ.c
  G := cPZ.G
  E := cPZ.E
  GI := cPZ.GI
  A := cPZ.mergedConsCol
  b := ConPolyZono.compactConsB cPZ
  EC := fun k l => cPZ.EC k (PolyZonotope.keepIdx cPZ.EC l)
  err := cPZ.err

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
