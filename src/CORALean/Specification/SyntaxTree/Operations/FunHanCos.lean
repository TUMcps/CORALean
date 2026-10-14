module

public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.Interval.Real.Operations.Intersection
public import CORALean.Specification.SyntaxTree.Operations.Interval
public import CORALean.Specification.SyntaxTree.Operations.Periodic
public import CORALean.Specification.SyntaxTree.SyntaxTree

@[expose] public section

/-!
# `aux_cos_`: the contraction of `cos`

`aux_cos_(int,intPrev)` of `syntaxTree.m`: the branches `acos(int)` and `-acos(int)`, shifted by
`2 pi k` (`aux_periodic_`).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `aux_cos_`: the branches `acos(int)` and `-acos(int)` shifted by `2 pi k`. -/
noncomputable def SyntaxTree.funHanCos (int prev : Dom) : Outcome Dom :=
  -- intersection with valid domain
  let int := Real.Interval.intersection int (interval (-1) 1)
  -- apply inverse function
  let resTemp₁ := Real.Interval.acos int
  let resTemp₂ := interval (-resTemp₁.sup 0) (-resTemp₁.inf 0)
  .ok (periodic resTemp₁ resTemp₂ prev)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
