import CORALean.ContSet.Interval.Float.Interval

/-!
# `Interval.representsa_emptySet`

The emptiness test at float: some coordinate with `sup` strictly below `inf`, by `ltStrict`. It
certifies emptiness only; a box whose crossing is under the margin is not reported.
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

def Interval.representsa_emptySet (I : Interval (Vec 𝕋 n)) : Bool :=
  (List.finRange n).any fun j => ltStrict (I.sup j) (I.inf j)


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
