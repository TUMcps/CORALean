module

public import CORALean.ContSet.Interval.Real.Operations.Atan
public import CORALean.ContSet.Interval.Real.Operations.Intersection
public import CORALean.Specification.SyntaxTree.Operations.Interval
public import CORALean.Specification.SyntaxTree.Operations.Periodic
public import CORALean.Specification.SyntaxTree.SyntaxTree

@[expose] public section

/-!
# `aux_tan_`, as printed

`aux_tan_(int,intPrev)` of `syntaxTree.m` begins with `int = int & interval(-1,1)`, copied from
`aux_sin_`, though `tan` takes every real value: the value `int` of the parent is cut to `[-1,1]`,
and
the contraction misses the solutions where `tan x > 1`. `SyntaxTree.funHanTan` is the function
without
that line; `SyntaxTree.tanCora_counterexample` the tree where the difference shows.

## Inputs
* `int` – target interval
* `prev` – previous interval

## Output
* the printed backpropagated interval of tan, or an empty outcome
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `aux_tan_` as printed: `int & interval(-1,1)`, the branches `atan(int)` and `atan(int) + pi`. -/
noncomputable def SyntaxTree.funHanTanCora (int prev : Dom) : Outcome Dom :=
  -- intersection with valid domain
  let int := Real.Interval.intersection int (interval (-1) 1)
  -- apply inverse function
  let resTemp₁ := Real.Interval.atan int
  let resTemp₂ := interval (resTemp₁.inf 0 + Real.pi) (resTemp₁.sup 0 + Real.pi)
  .ok (periodic resTemp₁ resTemp₂ prev)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
