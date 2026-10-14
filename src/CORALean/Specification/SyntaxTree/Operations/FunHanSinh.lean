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
  let temp₁ := Real.arsinh (int.inf 0)
  let temp₂ := Real.arsinh (int.sup 0)
  .ok (Real.Interval.intersection prev (interval (min temp₁ temp₂) (max temp₁ temp₂)))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
