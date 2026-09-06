import CORALean.ContSet.ConPolyZono.Float.Operations.CompactConsGap

/-!
# `ConPolyZono.compactConsB`

`b` widened by what a merged row can be off by. Every constraint monomial is
in `[-1,1]`, so a row's whole error is one `radius` of its gaps, and rounding
it outward on both sides is what keeps the constraint admitting what it did.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `b` widened by what a merged row can be off by. Every constraint monomial is
in `[-1,1]`, so a row's whole error is one `radius` of its gaps, and rounding it
outward on both sides is what keeps the constraint admitting what it did. -/
def ConPolyZono.compactConsB (C : ConPolyZono 𝕋 n) : Interval 𝕋 C.m :=
  ⟨fun i => subDown (C.b.inf i) (radius (ConPolyZono.compactConsGap C) i),
    fun i => addUp (C.b.sup i) (radius (ConPolyZono.compactConsGap C) i)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
