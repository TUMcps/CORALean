module

public import CORALean.ContSet.Interval.Real.Operations.Intersection
public import CORALean.Specification.SyntaxTree.Operations.Interval
public import CORALean.Specification.SyntaxTree.SyntaxTree

@[expose] public section

/-!
# `aux_sinh_`: the contraction of `sinh`

`aux_sinh_(int,intPrev)` of `syntaxTree.m` without its `int & interval(-1,1)` (`aux_sinhCora_`):
`asinh`
of `int`, met with `intPrev`.

## Inputs
* `int` – target interval
* `prev` – previous interval

## Output
* the interval of operands whose hyperbolic sine lies in the target
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `aux_sinh_`: `asinh(int)` met with `intPrev`. -/
noncomputable def SyntaxTree.funHanSinh (int prev : Dom) : Outcome Dom :=
  -- apply inverse function
  let preInf := Real.arsinh (int.inf 0)
  let preSup := Real.arsinh (int.sup 0)
  .ok (Real.Interval.intersection prev (interval (min preInf preSup) (max preInf preSup)))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
