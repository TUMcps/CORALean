module

public import CORALean.ContSet.Interval.Float.Operations.Asinh
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.Specification.SyntaxTree.Operations.FunHanSinh
public import CORALean.Specification.SyntaxTree.Operations.IntervalFloat

@[expose] public section

/-!
# `aux_sinh_` over a float scalar

`aux_sinh_(int,intPrev)` of `syntaxTree.m` with the bounds held in `𝕋`: `asinh` of `int` met with
`intPrev`. The inverse hyperbolic sine rounds outward (`Interval.asinh`). Soundness is
`SyntaxTree.funHanSinhFloat_sound`.

## Inputs
* `p` – precision of the logarithm
* `k` – bisection and root steps
* `int` – target interval
* `prev` – previous interval

## Output
* the interval of operands whose hyperbolic sine lies in the target
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

/-- `aux_sinh_`: `asinh(int)` met with `intPrev`, rounded outward. -/
def SyntaxTree.funHanSinhFloat (p k : ℕ) (int prev : Float.SyntaxTree.Dom 𝕋) :
    SyntaxTree.Outcome (Float.SyntaxTree.Dom 𝕋) :=
  .ok (Float.Interval.intersection prev (Float.Interval.asinh p k int))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
