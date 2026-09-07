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


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Equal constraint exponent columns added together, the stored value the lower
rounding and the widening paid into `b`. The generators stand, so the ambient
box is untouched. -/
def ConPolyZono.compactCons (cPZ : ConPolyZono 𝕋 n) : ConPolyZono 𝕋 n where
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
