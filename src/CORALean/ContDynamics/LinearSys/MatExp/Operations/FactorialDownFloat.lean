import CORALean.Global.Float.SoundFloatArithmetic

/-!
# `MatExp.factorialDown`, a float lower bound of a factorial

`k!` copies of `one`, summed with `nsmulDown`, and held above `one` by an exact
`maximum` — the same clamp `softmaxDenomDown` uses, so the reciprocal that
follows never meets a divisor the rounding says nothing about: `k! ≥ 1` always,
so the clamp discards nothing a sound bound needed.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def MatExp.factorialDown (k : ℕ) : 𝕋 := maximum one (nsmulDown (Nat.factorial k) one)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
