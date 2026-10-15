module

public import CORALean.ContSet.Interval.Real.Operations.Intersection
public import CORALean.Specification.SyntaxTree.Operations.Interval
public import CORALean.Specification.SyntaxTree.SyntaxTree

@[expose] public section

/-!
# `aaux_sin_`: the contraction of `asin`

`aaux_sin_(int,intPrev)` of `syntaxTree.m`: `sin` of `int` cut to `[-pi/2, pi/2]` below, met with
`intPrev`. An `int` below `-pi/2` throws `CORA:outOfDomain`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `aaux_sin_`: `sin(int)`, with `int` cut to `[-pi/2, pi/2]` below, met with `intPrev`. -/
noncomputable def SyntaxTree.funHanAsin (int prev : Dom) : Outcome Dom :=
  let step := fun (int : Dom) =>
    -- apply inverse function
    let preInf := Real.sin (int.inf 0)
    let preSup := Real.sin (int.sup 0)
    Outcome.ok (Real.Interval.intersection prev (interval (min preInf preSup) (max preInf preSup)))
  -- intersection with valid domain
  if int.inf 0 < -(Real.pi / 2) then
    if int.sup 0 < -(Real.pi / 2) then .outOfDomain else step (interval (-(Real.pi / 2)) (Real.pi /
        2))
  else step int

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
