module

public import CORALean.ContSet.Interval.Real.Operations.Intersection
public import CORALean.Specification.SyntaxTree.Operations.Interval
public import CORALean.Specification.SyntaxTree.SyntaxTree

@[expose] public section

/-!
# `aux_sinh_`, as printed

`aux_sinh_(int,intPrev)` of `syntaxTree.m` begins with `int = int & interval(-1,1)`, copied from the
circular functions, though `sinh` takes every real value: a target `int` beyond `[-1,1]` is cut,
and the
contraction loses the solutions with `|sinh x| > 1`. `SyntaxTree.funHanSinh` is the function without
that line; `SyntaxTree.sinhCora_counterexample` the tree where the difference shows.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `aux_sinh_` as printed: `asinh(int & interval(-1,1))` met with `intPrev`. -/
noncomputable def SyntaxTree.funHanSinhCora (int prev : Dom) : Outcome Dom :=
  -- intersection with valid domain
  let int := Real.Interval.intersection int (interval (-1) 1)
  -- apply inverse function
  let temp₁ := Real.arsinh (int.inf 0)
  let temp₂ := Real.arsinh (int.sup 0)
  .ok (Real.Interval.intersection prev (interval (min temp₁ temp₂) (max temp₁ temp₂)))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
