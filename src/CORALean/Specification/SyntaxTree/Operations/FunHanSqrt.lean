module

public import CORALean.ContSet.Interval.Real.Operations.Intersection
public import CORALean.Specification.SyntaxTree.Operations.Interval
public import CORALean.Specification.SyntaxTree.SyntaxTree

@[expose] public section

/-!
# `aux_sqrt_`: the contraction of `sqrt`

`aux_sqrt_(int,intPrev)` of `syntaxTree.m`: the squares of `int` cut to the nonnegative reals, met
with
`intPrev`. An `int` below `0` throws `CORA:outOfDomain`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `aux_sqrt_`: the squares of `int` cut to `≥ 0`, met with `intPrev`. -/
noncomputable def SyntaxTree.funHanSqrt (int prev : Dom) : Outcome Dom :=
  let step := fun (int : Dom) =>
    let temp₁ := (int.inf 0) ^ 2
    let temp₂ := (int.sup 0) ^ 2
    Outcome.ok (Real.Interval.intersection prev (interval (min temp₁ temp₂) (max temp₁ temp₂)))
  if int.inf 0 < 0 then
    if int.sup 0 < 0 then .outOfDomain else step (interval 0 (int.sup 0))
  else step int

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
