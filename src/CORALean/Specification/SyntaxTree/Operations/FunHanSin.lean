module

public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.Interval.Real.Operations.Intersection
public import CORALean.Specification.SyntaxTree.Operations.Interval
public import CORALean.Specification.SyntaxTree.Operations.Periodic
public import CORALean.Specification.SyntaxTree.SyntaxTree

@[expose] public section

/-!
# `aux_sin_`: the contraction of `sin`

`aux_sin_(int,intPrev)` of `syntaxTree.m`: the branches `asin(int)` and `pi - asin(int)`, shifted by
`2 pi k` (`aux_periodic_`).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `aux_sin_`: the branches `asin(int)` and `pi - asin(int)` shifted by `2 pi k`. -/
noncomputable def SyntaxTree.funHanSin (int prev : Dom) : Outcome Dom :=
  -- intersection with valid domain
  let int := Real.Interval.intersection int (interval (-1) 1)
  -- apply inverse function
  let resTemp₁ := Real.Interval.asin int
  let resTemp₂ := interval (Real.pi - resTemp₁.sup 0) (Real.pi - resTemp₁.inf 0)
  .ok (periodic resTemp₁ resTemp₂ prev)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
