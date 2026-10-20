module

public import CORALean.ContSet.Interval.Real.Operations.Intersection
public import CORALean.Specification.SyntaxTree.Operations.Interval
public import CORALean.Specification.SyntaxTree.SyntaxTree

@[expose] public section

/-!
# `aaux_tanh_`: the contraction of `atanh`

`aaux_tanh_(int,intPrev)` of `syntaxTree.m`: `tanh` of `int`, met with `intPrev`.

## Inputs
* `int` – target interval
* `prev` – previous interval

## Output
* the interval for the operand of the inverse hyperbolic tangent
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `aaux_tanh_`: `tanh(int)` met with `intPrev`. -/
noncomputable def SyntaxTree.funHanAtanh (int prev : Dom) : Outcome Dom :=
  -- apply inverse function
  let preInf := Real.tanh (int.inf 0)
  let preSup := Real.tanh (int.sup 0)
  .ok (Real.Interval.intersection prev (interval (min preInf preSup) (max preInf preSup)))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
