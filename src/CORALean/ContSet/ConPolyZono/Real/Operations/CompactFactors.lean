import CORALean.ContSet.ConPolyZono.Real.Operations.FactorIdx

/-!
# `ConPolyZono.compactFactors`

The factors neither block reads, dropped. Only `p` and the two exponent
matrices change; every generator, every constraint column and `b` stand.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The factors neither block reads, dropped. Only `p` and the two exponent
matrices change; every generator, every constraint column and `b` stand. -/
def ConPolyZono.compactFactors (C : ConPolyZono α) : ConPolyZono α where
  p := (ConPolyZono.usedFactors C.E C.EC).card
  h := C.h
  q := C.q
  m := C.m
  s := C.s
  c := C.c
  G := C.G
  E := fun k i => C.E (ConPolyZono.factorIdx C.E C.EC k) i
  GI := C.GI
  A := C.A
  b := C.b
  EC := fun k l => C.EC (ConPolyZono.factorIdx C.E C.EC k) l

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
