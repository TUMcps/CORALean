module

public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# `MatExp.factorialDown`, a float lower bound of a factorial

`k! = k · (k-1)!`, one `mulDown` per factor, each factor `k` counted up from
`one` by `nsmulDown` and clamped at `zero`, so a product of two lower bounds is
one; `k` multiplications, not the `k!` additions a count of copies would take.
Each partial product is held above `one` by an exact `maximum` — the clamp
`softmaxDenomDown` uses, so the reciprocal that follows never meets a divisor
the rounding says nothing about: `k! ≥ 1` always, so it discards nothing.

## Inputs
* none

## Output
* float lower bounds of the factorials
-/

-- Authors:       Claude Sonnet 5
-- Written:       24-September-2026
-- Last update:   25-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def MatExp.factorialDown : ℕ → 𝕋
  | 0 => one
  | k + 1 => maximum one (mulDown (maximum zero (nsmulDown (k + 1) one)) (MatExp.factorialDown k))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
