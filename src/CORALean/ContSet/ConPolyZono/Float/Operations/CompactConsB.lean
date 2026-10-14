module

public import CORALean.ContSet.ConPolyZono.Float.Operations.Basic

@[expose] public section

/-!
# `ConPolyZono.compactConsB`

`b` widened by what a merged row can be off by. Every constraint monomial is
in `[-1,1]`, so a row's whole error is one `radius` of its gaps, and rounding
it outward on both sides is what keeps the constraint admitting what it did.
-/

-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `b` widened by what a merged row can be off by. Every constraint monomial is
in `[-1,1]`, so a row's whole error is one `radius` of its gaps, and rounding it
outward on both sides is what keeps the constraint admitting what it did. -/
def ConPolyZono.compactConsB (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) : Interval (Vec 𝕋 cPZ.m) :=
  ⟨fun i => subDown (cPZ.b.inf i) (radius (ConPolyZono.compactConsGap cPZ) i),
    fun i => addUp (cPZ.b.sup i) (radius (ConPolyZono.compactConsGap cPZ) i)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
