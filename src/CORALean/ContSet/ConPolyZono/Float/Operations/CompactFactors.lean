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

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- The factors neither block reads, dropped. Only `p` and the two exponent
matrices change, all over ℕ, so nothing rounds and neither `b` nor the box
moves. -/
def ConPolyZono.compactFactors (C : ConPolyZono 𝕋 n) : ConPolyZono 𝕋 n where
  p := (Real.ConPolyZono.usedFactors C.E C.EC).card
  h := C.h
  q := C.q
  m := C.m
  s := C.s
  c := C.c
  G := C.G
  E := fun k i => C.E (Real.ConPolyZono.factorIdx C.E C.EC k) i
  GI := C.GI
  A := C.A
  b := C.b
  EC := fun k l => C.EC (Real.ConPolyZono.factorIdx C.E C.EC k) l
  err := C.err

end CORALean.Float
