import CORALean.ContSet.ConPolyZono.Float.ConPolyZono
import CORALean.ContSet.ConPolyZono.Real.Operations.FactorIdx
import CORALean.ContSet.ConPolyZono.Real.Operations.UsedFactors

/-!
# `ConPolyZono.compactFactors`

The factors neither block reads, dropped. Only `p` and the two exponent
matrices change, all over ℕ, so nothing rounds and neither `b` nor the box
moves.
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

/-- The factors neither block reads, dropped. Only `p` and the two exponent
matrices change, all over ℕ, so nothing rounds and neither `b` nor the box
moves. -/
def ConPolyZono.compactFactors (cPZ : ConPolyZono 𝕋 n) : ConPolyZono 𝕋 n where
  p := (Real.ConPolyZono.usedFactors cPZ.E cPZ.EC).card
  h := cPZ.h
  q := cPZ.q
  m := cPZ.m
  s := cPZ.s
  c := cPZ.c
  G := cPZ.G
  E := fun k i => cPZ.E (Real.ConPolyZono.factorIdx cPZ.E cPZ.EC k) i
  GI := cPZ.GI
  A := cPZ.A
  b := cPZ.b
  EC := fun k l => cPZ.EC (Real.ConPolyZono.factorIdx cPZ.E cPZ.EC k) l
  err := cPZ.err

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
