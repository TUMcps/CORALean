module

public import CORALean.ContSet.ConPolyZono.Real.Operations.Basic

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
  p := (ConPolyZono.usedFactors cPZ.E cPZ.R).card
  h := cPZ.h
  qI := cPZ.qI
  m := cPZ.m
  q := cPZ.q
  c := cPZ.c
  G := cPZ.G
  E := fun k i => cPZ.E (ConPolyZono.factorIdx cPZ.E cPZ.R k) i
  GI := cPZ.GI
  A := cPZ.A
  b := cPZ.b
  R := fun k l => cPZ.R (ConPolyZono.factorIdx cPZ.E cPZ.R k) l

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
