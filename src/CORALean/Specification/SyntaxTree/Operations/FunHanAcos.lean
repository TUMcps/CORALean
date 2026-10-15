module

public import CORALean.ContSet.Interval.Real.Operations.Intersection
public import CORALean.Specification.SyntaxTree.Operations.Interval
public import CORALean.Specification.SyntaxTree.SyntaxTree

@[expose] public section

/-!
# `aaux_cos_`: the contraction of `acos`

`aaux_cos_(int,intPrev)` of `syntaxTree.m`: `cos` of `int` cut to `[0,∞)`, met with `intPrev`. An
`int`
below `0` throws `CORA:outOfDomain`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `aaux_cos_`: `cos(int)`, with `int` cut to `≥ 0`, met with `intPrev`. -/
noncomputable def SyntaxTree.funHanAcos (int prev : Dom) : Outcome Dom :=
  let step := fun (int : Dom) =>
    -- apply inverse function
    let preInf := Real.cos (int.inf 0)
    let preSup := Real.cos (int.sup 0)
    Outcome.ok (Real.Interval.intersection prev (interval (min preInf preSup) (max preInf preSup)))
  -- intersection with valid domain
  if int.inf 0 < 0 then
    if int.sup 0 < 0 then .outOfDomain else step (interval 0 (int.sup 0))
  else step int

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
