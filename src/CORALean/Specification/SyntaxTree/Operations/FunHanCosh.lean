module

public import CORALean.ContSet.Interval.Real.Operations.Intersection
public import CORALean.Specification.SyntaxTree.Operations.Interval
public import CORALean.Specification.SyntaxTree.Operations.SignedRoots
public import CORALean.Specification.SyntaxTree.SyntaxTree

@[expose] public section

/-!
# `aux_cosh_`: the contraction of `cosh`

`aux_cosh_(int,intPrev)` of `syntaxTree.m`: `acosh` of `int` cut to the reals `≥ 1`, with the sign
`intPrev`
allows (`[-m, m]` when it contains `0`), met with `intPrev`. An `int` below `1` throws
`CORA:outOfDomain`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `aux_cosh_`: `acosh(int)` cut to `≥ 1`, with the sign `intPrev` allows. -/
noncomputable def SyntaxTree.funHanCosh (int prev : Dom) : Outcome Dom :=
  let step := fun (int : Dom) =>
    -- apply inverse function
    let temp₁ := Real.arcosh (int.inf 0)
    let temp₂ := Real.arcosh (int.sup 0)
    Outcome.ok (Real.Interval.intersection prev (signedRoots prev temp₁ temp₂))
  -- intersection with valid domain
  if int.inf 0 < 1 then
    if int.sup 0 < 1 then .outOfDomain else step (interval 1 (int.sup 0))
  else step int

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
