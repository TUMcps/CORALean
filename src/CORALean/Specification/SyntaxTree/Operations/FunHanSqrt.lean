module

public import CORALean.ContSet.Interval.Real.Operations.Intersection
public import CORALean.Specification.SyntaxTree.Operations.Interval
public import CORALean.Specification.SyntaxTree.SyntaxTree

@[expose] public section

/-!
# `aux_sqrt_`: the contraction of `sqrt`

`aux_sqrt_(int,intPrev)` of `syntaxTree.m`: the squares of `int` cut to the nonnegative reals, met
with
`intPrev`. An `int` below `0` throws `CORA:outOfDomain`.

## Inputs
* `int` – target interval
* `prev` – previous interval

## Output
* the interval of operands whose square root lies in the target
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `aux_sqrt_`: the squares of `int` cut to `≥ 0`, met with `intPrev`. -/
noncomputable def SyntaxTree.funHanSqrt (int prev : Dom) : Outcome Dom :=
  let step := fun (int : Dom) =>
    let preInf := (int.inf 0) ^ 2
    let preSup := (int.sup 0) ^ 2
    Outcome.ok (Real.Interval.intersection prev (interval (min preInf preSup) (max preInf preSup)))
  if int.inf 0 < 0 then
    if int.sup 0 < 0 then .outOfDomain else step (interval 0 (int.sup 0))
  else step int

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
