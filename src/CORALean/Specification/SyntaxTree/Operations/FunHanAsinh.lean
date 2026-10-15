module

public import CORALean.ContSet.Interval.Real.Operations.Intersection
public import CORALean.Specification.SyntaxTree.Operations.Interval
public import CORALean.Specification.SyntaxTree.SyntaxTree

@[expose] public section

/-!
# `aaux_sinh_`: the contraction of `asinh`

`aaux_sinh_(int,intPrev)` of `syntaxTree.m`: `sinh` of `int`, met with `intPrev`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `aaux_sinh_`: `sinh(int)` met with `intPrev`. -/
noncomputable def SyntaxTree.funHanAsinh (int prev : Dom) : Outcome Dom :=
  -- apply inverse function
  let preInf := Real.sinh (int.inf 0)
  let preSup := Real.sinh (int.sup 0)
  .ok (Real.Interval.intersection prev (interval (min preInf preSup) (max preInf preSup)))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
