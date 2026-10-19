module

public import CORALean.ContSet.PolyLevelSet.Float.Operations.Basic

@[expose] public section

/-!
# `PolyLevelSet.compactSpec`

Equal exponent columns merged, the stored coefficients the lower rounding and the widening paid
into the slack `b_error` (`compactSlack`). The definition `compact` is proved equal to, which
computes the same thing from tables built once (issue #61). This one is the statement the
soundness proof reads: every entry a named, separately provable lookup.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The specification of `compact`: equal exponent columns merged, the stored coefficients
rounded down and the slack widened by what they can be off by. -/
def PolyLevelSet.compactSpec (P : PolyLevelSet 𝕋 n) : PolyLevelSet 𝕋 n where
  m := P.m
  q := (PolyZonotope.repKeep P.R).card
  A := P.mergedCol
  R := fun k l => P.R k (PolyZonotope.keepIdx P.R l)
  b := P.b
  b_error := P.compactSlack
  op := P.op

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
