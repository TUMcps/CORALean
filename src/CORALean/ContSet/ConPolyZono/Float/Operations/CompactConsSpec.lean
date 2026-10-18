module

public import CORALean.ContSet.ConPolyZono.Float.Operations.CompactConsB
public import CORALean.ContSet.ConPolyZono.Float.Operations.Basic

@[expose] public section

/-!
# `ConPolyZono.compactConsSpec`

Equal constraint exponent columns added together, the stored value the lower
rounding and the widening paid into the slack `b_error`. The generators stand, so the ambient
box is untouched.

The definition `compactCons` is proved equal to, which computes the same thing
from tables built once (issue #61). This one is the statement the soundness proof
reads: every entry a named, separately provable lookup.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The specification of `compactCons`: equal constraint exponent columns added
together, the stored value the lower rounding and the widening paid into `b_error`.
The generators stand, so the ambient box is untouched. -/
def ConPolyZono.compactConsSpec (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) : ConPolyZono 𝕋 (Vec 𝕋 n) where
  p := cPZ.p
  h := cPZ.h
  qI := cPZ.qI
  m := cPZ.m
  q := (PolyZonotope.repKeep cPZ.R).card
  c := cPZ.c
  G := cPZ.G
  E := cPZ.E
  GI := cPZ.GI
  A := cPZ.mergedConsCol
  b := cPZ.b
  b_error := ConPolyZono.compactConsB cPZ
  R := fun k l => cPZ.R k (PolyZonotope.keepIdx cPZ.R l)
  I_error := cPZ.I_error

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
