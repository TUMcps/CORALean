module

public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `Interval.isFullDim`

A test for full dimension at float: `ltStrict` on `inf i` and `sup i` in every coordinate, asking
for a positive width, so `true` is certain and `false` only says "not shown".
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.isFullDim (I : Interval (Vec 𝕋 n)) : Bool :=
  (List.finRange n).all fun j => ltStrict (I.inf j) (I.sup j)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
