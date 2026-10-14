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
  let temp₁ := Real.sinh (int.inf 0)
  let temp₂ := Real.sinh (int.sup 0)
  .ok (Real.Interval.intersection prev (interval (min temp₁ temp₂) (max temp₁ temp₂)))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
