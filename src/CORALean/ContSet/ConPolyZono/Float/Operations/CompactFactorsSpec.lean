module

public import CORALean.ContSet.PolyLevelSet.Float.Operations.ReindexVars
public import CORALean.ContSet.ConPolyZono.Float.ConPolyZono

@[expose] public section

/-!
# `ConPolyZono.compactFactorsSpec`

The factors neither block reads, dropped. Only `p` and the two exponent
matrices change, all over ℕ, so nothing rounds and neither `b` nor the box
moves. The constraint is its own `PolyLevelSet.reindexVars` at the used factors.

The definition `compactFactors` is proved equal to, which computes the same thing
from a table built once (issue #61); this one is the statement the exactness
proof reads.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The specification of `compactFactors`: the factors neither block reads, dropped.
Only `p` and the two exponent matrices change, all over ℕ, so nothing rounds and
neither `b` nor the box moves. -/
def ConPolyZono.compactFactorsSpec (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) :
    ConPolyZono 𝕋 (Vec 𝕋 n) where
  p := (Real.ConPolyZono.usedFactors cPZ.E cPZ.cons.R).card
  h := cPZ.h
  qI := cPZ.qI
  c := cPZ.c
  G := cPZ.G
  E := fun k i => cPZ.E (Real.ConPolyZono.factorIdx cPZ.E cPZ.cons.R k) i
  GI := cPZ.GI
  cons := cPZ.cons.reindexVars (Real.ConPolyZono.factorIdx cPZ.E cPZ.cons.R)
  cons_eq := cPZ.cons_eq
  I_error := cPZ.I_error

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
