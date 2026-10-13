module

public import CORALean.ContSet.ConPolyZono.Float.ConPolyZono
public import CORALean.ContSet.ConPolyZono.Real.Operations.FactorIdx
public import CORALean.ContSet.ConPolyZono.Real.Operations.UsedFactors

@[expose] public section

/-!
# `ConPolyZono.compactFactorsSpec`

The factors neither block reads, dropped. Only `p` and the two exponent
matrices change, all over ℕ, so nothing rounds and neither `b` nor the box
moves.

The definition `compactFactors` is proved equal to, which computes the same thing
from a table built once (issue #61); this one is the statement the exactness
proof reads.
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

/-- The specification of `compactFactors`: the factors neither block reads, dropped.
Only `p` and the two exponent matrices change, all over ℕ, so nothing rounds and
neither `b` nor the box moves. -/
def ConPolyZono.compactFactorsSpec (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) : ConPolyZono 𝕋 (Vec 𝕋 n) where
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
