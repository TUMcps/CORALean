import CORALean.Global.Float.SoundFloatArithmetic

/-!
# `MatExp.corrCoeffLow`, a float lower bound of the correction coefficient

`Real.MatExp.corrCoeff i = a^i - a` at `a = i^(-1/(i-1))` is an `rpow`, which
no float format computes soundly. Since `a^(i-1) = 1/i`, the coefficient is
`-(1 - 1/i)·a`, and Bernoulli's inequality puts `a` below `1 - 1/i`; so
`-(1 - 1/i)²` bounds it from below, exactly at `i = 2`, the order a short step
is dominated by, and within `0.06` at `i = 3`.
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

/-- `-(1 - 1/i)²`, rounded down: `(i - 1)/i` over a denominator held between
`1` and `i`, squared upwards, then negated exactly. -/
def MatExp.corrCoeffLow (i : ℕ) : 𝕋 :=
  let q := divUp (nsmulUp (i - 1) one) (maximum one (nsmulDown i one))  -- q ≥ (i - 1)/i
  neg (mulUp q q)                                                       -- -q² ≤ -(1 - 1/i)²

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
