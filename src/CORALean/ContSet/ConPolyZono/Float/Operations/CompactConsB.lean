module

public import CORALean.ContSet.ConPolyZono.Float.Operations.Basic

@[expose] public section

/-!
# `ConPolyZono.compactConsB`

The slack widened by what a merged row can be off by. Every constraint monomial is
in `[-1,1]`, so a row's whole error is one `radius` of its gaps, and adding it, rounded up, to
the slack is what keeps the constraint admitting what it did.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The slack widened by what a merged row can be off by: one `radius` of the row's gaps,
every constraint monomial being in `[-1,1]`. -/
def ConPolyZono.compactConsB (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) : Vec 𝕋 cPZ.cons.m :=
  fun i => addUp (absolute (cPZ.cons.b_error i)) (radius (ConPolyZono.compactConsGap cPZ) i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
