module

public import CORALean.ContSet.Interval.Real.Operations.Intersection
public import CORALean.Specification.SyntaxTree.Operations.Interval
public import CORALean.Specification.SyntaxTree.SyntaxTree

@[expose] public section

/-!
# `aux_log_`: the contraction of `log`

`aux_log_(int,intPrev)` of `syntaxTree.m`: `exp` of `int`, met with `intPrev`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `aux_log_`: `exp(int)` met with `intPrev`. -/
noncomputable def SyntaxTree.funHanLog (int prev : Dom) : Outcome Dom :=
  let temp₁ := Real.exp (int.inf 0)
  let temp₂ := Real.exp (int.sup 0)
  .ok (Real.Interval.intersection prev (interval (min temp₁ temp₂) (max temp₁ temp₂)))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
