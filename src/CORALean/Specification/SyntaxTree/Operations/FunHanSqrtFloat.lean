module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Operations.Power
public import CORALean.Specification.SyntaxTree.Operations.FunHanSqrt
public import CORALean.Specification.SyntaxTree.Operations.IntervalFloat

@[expose] public section

/-!
# `aux_sqrt_` over a float scalar

`aux_sqrt_(int,intPrev)` of `syntaxTree.m` with the bounds held in `𝕋`: the squares of `int` cut to
the nonnegative reals, met with `intPrev`. The square rounds outward (`Interval.power`). An `int`
certified below `0` throws `CORA:outOfDomain`. Soundness is `SyntaxTree.funHanSqrtFloat_sound`.

## Inputs
* `int` – target interval
* `prev` – previous interval

## Output
* the interval of operands whose square root lies in the target
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

/-- `aux_sqrt_`: the squares of `int` cut to `≥ 0`, met with `intPrev`, rounded outward. -/
def SyntaxTree.funHanSqrtFloat (int prev : Float.SyntaxTree.Dom 𝕋) :
    SyntaxTree.Outcome (Float.SyntaxTree.Dom 𝕋) :=
  if ltStrict (int.sup 0) zero = true then .outOfDomain
  else
    -- `int` cut to the nonnegative reals
    let cut : Float.SyntaxTree.Dom 𝕋 := ⟨fun _ => maximum (int.inf 0) zero, fun _ => int.sup 0⟩
    .ok (Float.Interval.intersection prev (Float.Interval.power cut 2))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
