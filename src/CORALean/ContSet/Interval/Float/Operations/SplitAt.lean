module

public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `Interval.splitAt` over floats

Bisect one coordinate at its midpoint. The midpoint is rounded, so the two halves reach past it
in opposite directions: the first half's `sup` takes the midpoint rounded up and the second half's
`inf` takes it rounded down. They overlap by at most the rounding, and so still cover the box
(`Theorems/SplitAtCover`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.splitAt (I : Interval (Vec 𝕋 n)) (j : Fin n) :
    Interval (Vec 𝕋 n) × Interval (Vec 𝕋 n) :=
  (⟨I.inf, Function.update I.sup j (half (addUp (I.inf j) (I.sup j)))⟩,
   ⟨Function.update I.inf j (half (addDown (I.inf j) (I.sup j))), I.sup⟩)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
