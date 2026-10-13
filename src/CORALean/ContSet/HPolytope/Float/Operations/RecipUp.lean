module

public import CORALean.ContSet.HPolytope.Float.Operations.RowScale

@[expose] public section

/-!
# `recipUp`: a positive scale from a number

`1 / a` rounded up when `ltStrict` certifies `a` positive, and `1` otherwise (CORA leaves a
zero divisor alone). A positive number either way, which is all a row scaling needs: a row scaled
by a positive number is the same halfspace.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]  {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `1 / a` from above at a certified positive `a`, else `1`. -/
def HPolytope.recipUp (a : 𝕋) : 𝕋 :=
  if ltStrict zero a then divUp one a else one

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
