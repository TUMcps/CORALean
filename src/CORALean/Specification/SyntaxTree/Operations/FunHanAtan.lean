module

public import CORALean.Specification.SyntaxTree.SyntaxTree
public import CORALean.Specification.SyntaxTree.Operations.Restrict
public import CORALean.Specification.SyntaxTree.Operations.Interval

@[expose] public section

/-!
# `aaux_tan_`: the contraction of `atan`

`aaux_tan_(int,intPrev)` of `syntaxTree.m`: `tan` of `int` cut to `[-pi/2, pi/2]` below
(`tan(±pi/2) =
±Inf`), met with `intPrev`. An `int` below `-pi/2` throws `CORA:outOfDomain`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `aaux_tan_`: `tan(int)`, with `int` cut to `[-pi/2, pi/2]` below, met with `intPrev`. -/
noncomputable def SyntaxTree.funHanAtan (int prev : Dom) : Outcome Dom :=
  let step := fun (int : Dom) =>
    -- apply inverse function, `tan(±pi/2) = ±Inf`
    let tanE := fun (x : ℝ) =>
      (if x = -(Real.pi / 2) then ⊥ else if x = Real.pi / 2 then ⊤ else ↑(Real.tan x) : EReal)
    let preInf := tanE (int.inf 0)
    let preSup := tanE (int.sup 0)
    Outcome.ok (restrict prev (min preInf preSup) (max preInf preSup))
  -- intersection with valid domain
  if int.inf 0 < -(Real.pi / 2) then
    if int.sup 0 < -(Real.pi / 2) then .outOfDomain else step (interval (-(Real.pi / 2)) (Real.pi /
        2))
  else step int

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
