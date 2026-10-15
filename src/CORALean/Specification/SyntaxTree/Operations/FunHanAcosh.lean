module

public import CORALean.ContSet.Interval.Real.Operations.Intersection
public import CORALean.Specification.SyntaxTree.Operations.Interval
public import CORALean.Specification.SyntaxTree.SyntaxTree

@[expose] public section

/-!
# `aaux_cosh_`: the contraction of `acosh`

`aaux_cosh_(int,intPrev)` of `syntaxTree.m`: `cosh` of `int` cut to `[0,∞)`, met with `intPrev`. An
`int` below `0` throws `CORA:outOfDomain`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `aaux_cosh_`: `cosh(int)`, with `int` cut to `≥ 0`, met with `intPrev`. -/
noncomputable def SyntaxTree.funHanAcosh (int prev : Dom) : Outcome Dom :=
  let step := fun (int : Dom) =>
    -- apply inverse function
    let preInf := Real.cosh (int.inf 0)
    let preSup := Real.cosh (int.sup 0)
    Outcome.ok (Real.Interval.intersection prev (interval (min preInf preSup) (max preInf preSup)))
  -- intersection with valid domain
  if int.inf 0 < 0 then
    if int.sup 0 < 0 then .outOfDomain else step (interval 0 (int.sup 0))
  else step int

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
