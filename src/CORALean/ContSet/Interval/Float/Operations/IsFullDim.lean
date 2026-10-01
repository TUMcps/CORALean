import CORALean.ContSet.Interval.Float.Interval

/-!
# `Interval.isFullDim`

A test for full dimension at float: `ltStrict` on `inf i` and `sup i` in every coordinate, asking
for a positive width, so `true` is certain and `false` only says "not shown".
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.isFullDim (I : Interval (Vec 𝕋 n)) : Bool :=
  (List.finRange n).all fun j => ltStrict (I.inf j) (I.sup j)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
