import CORALean.Global.Float.Exp

/-!
# `1 + eᵃ` from below, never below one

The denominator of the logistic function, underestimated through `expDown` — a lower bound on
an exponential is the one direction available without a hypothesis on the argument — and held
above one by an exact `maximum`, so a division by it never meets a divisor the arithmetic
constrains in no way.
-/

-- Authors:       Tobias Ladner
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `1 + exp a` from below, never below one. -/
def onePlusExpDown (k : ℕ) (a : 𝕋) : 𝕋 := maximum one (addDown one (expDown k a))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
