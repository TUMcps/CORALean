module

public import CORALean.ContSet.Interval.Float.Interval
public import CORALean.Global.Float.PowUp
public import CORALean.Global.Float.PowDown

@[expose] public section

/-!
# `Interval.powLo`, over a floating-point scalar

A lower bound on `a ^ k` for a scalar `a` of either sign, the mirror of `Interval.powHi`. An even
power is `powDown |a|`; an odd one is `powDown a` for a certified `a ≥ 0`, and `-(powUp |a|)`
otherwise, since `a ^ k ≥ -|a| ^ k` for every sign.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.powLo (a : 𝕋) (k : ℕ) : 𝕋 :=
  if k % 2 = 0 then powDown (absolute a) k
  else if le zero a = true then powDown a k
  else neg (powUp (absolute a) k)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
