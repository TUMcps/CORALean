import CORALean.ContSet.Interval.Float.Interval
import CORALean.Global.Float.PowUp
import CORALean.Global.Float.PowDown

/-!
# `Interval.powHi`, over a floating-point scalar

An upper bound on `a ^ k` for a scalar `a` of either sign. `powUp` and `powDown` ask for a
nonnegative base, so the sign is read off by `le`, whose `true` certifies it: an even power is
that of `|a|`; an odd one is `powUp a` for `a ≥ 0`, and `-(powDown |a|)` for `a ≤ 0`, where
`a ^ k = -|a| ^ k`; when neither sign is certified, `powUp |a|` bounds both.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.powHi (a : 𝕋) (k : ℕ) : 𝕋 :=
  if k % 2 = 0 then powUp (absolute a) k
  else if le zero a = true then powUp a k
  else if le a zero = true then neg (powDown (absolute a) k)
  else powUp (absolute a) k

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
