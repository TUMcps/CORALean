module

public import CORALean.ContSet.ConPolyZono.Real.Operations.FactorIdx

@[expose] public section

/-!
# `ConPolyZono.compactFactors`

The factors neither block reads, dropped. Only `p` and the two exponent
matrices change; every generator, every constraint column and `b` stand.
-/

-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The factors neither block reads, dropped. Only `p` and the two exponent
matrices change; every generator, every constraint column and `b` stand. -/
def ConPolyZono.compactFactors (cPZ : ConPolyZono α) : ConPolyZono α where
  p := (ConPolyZono.usedFactors cPZ.E cPZ.EC).card
  h := cPZ.h
  q := cPZ.q
  m := cPZ.m
  s := cPZ.s
  c := cPZ.c
  G := cPZ.G
  E := fun k i => cPZ.E (ConPolyZono.factorIdx cPZ.E cPZ.EC k) i
  GI := cPZ.GI
  A := cPZ.A
  b := cPZ.b
  EC := fun k l => cPZ.EC (ConPolyZono.factorIdx cPZ.E cPZ.EC k) l

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
