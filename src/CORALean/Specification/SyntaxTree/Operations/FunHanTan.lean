module

public import CORALean.ContSet.Interval.Real.Operations.Atan
public import CORALean.Specification.SyntaxTree.Operations.Interval
public import CORALean.Specification.SyntaxTree.Operations.Periodic
public import CORALean.Specification.SyntaxTree.SyntaxTree

@[expose] public section

/-!
# `aux_tan_`: the contraction of `tan`

`aux_tan_(int,intPrev)` of `syntaxTree.m` without its `int & interval(-1,1)` (`aux_tanCora_`): the
branches `atan(int)` and `atan(int) + pi`, shifted by `2 pi k` (`aux_periodic_`).

## Inputs
* `int` – target interval
* `prev` – previous interval

## Output
* the interval of operands whose tangent lies in the target
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `aux_tan_`: the branches `atan(int)` and `atan(int) + pi` shifted by `2 pi k`. -/
noncomputable def SyntaxTree.funHanTan (int prev : Dom) : Outcome Dom :=
  -- apply inverse function
  let resTemp₁ := Real.Interval.atan int
  let resTemp₂ := interval (resTemp₁.inf 0 + Real.pi) (resTemp₁.sup 0 + Real.pi)
  .ok (periodic resTemp₁ resTemp₂ prev)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
