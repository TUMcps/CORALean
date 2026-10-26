module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.Specification.SyntaxTree.Operations.FunHanLog
public import CORALean.Specification.SyntaxTree.Operations.IntervalFloat

@[expose] public section

/-!
# `aux_log_` over a float scalar

`aux_log_(int,intPrev)` of `syntaxTree.m` with the bounds held in `𝕋`: `exp` of `int`, met with
`intPrev`. The exponential rounds outward (`Interval.exp`). Soundness is
`SyntaxTree.funHanLogFloat_sound`.

## Inputs
* `p` – precision of the exponential
* `int` – target interval
* `prev` – previous interval

## Output
* the interval of operands whose logarithm lies in the target
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `aux_log_`: `exp(int)` met with `intPrev`, rounded outward. -/
def SyntaxTree.funHanLogFloat (p : ℕ) (int prev : Float.SyntaxTree.Dom 𝕋) :
    SyntaxTree.Outcome (Float.SyntaxTree.Dom 𝕋) :=
  .ok (Float.Interval.intersection prev (Float.Interval.exp p int))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
