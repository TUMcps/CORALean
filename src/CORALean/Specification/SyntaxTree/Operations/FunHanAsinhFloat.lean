module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.Specification.SyntaxTree.Operations.FunHanAsinh
public import CORALean.Specification.SyntaxTree.Operations.IntervalFloat

@[expose] public section

/-!
# `aaux_sinh_` over a float scalar

`aaux_sinh_(int,intPrev)` of `syntaxTree.m` with the bounds held in `𝕋`: `sinh` of `int` met with
`intPrev`. The hyperbolic sine rounds outward (`Interval.sinh`). Soundness is
`SyntaxTree.funHanAsinhFloat_sound`.

## Inputs
* `p` – precision of the hyperbolic sine
* `int` – target interval
* `prev` – previous interval

## Output
* the interval of operands whose inverse hyperbolic sine lies in the target
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

/-- `aaux_sinh_`: `sinh(int)` met with `intPrev`, rounded outward. -/
def SyntaxTree.funHanAsinhFloat (p : ℕ) (int prev : Float.SyntaxTree.Dom 𝕋) :
    SyntaxTree.Outcome (Float.SyntaxTree.Dom 𝕋) :=
  .ok (Float.Interval.intersection prev (Float.Interval.sinh p int))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
