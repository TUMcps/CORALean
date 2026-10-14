module

public import CORALean.Specification.SyntaxTree.SyntaxTree
public import CORALean.Specification.SyntaxTree.Operations.Restrict
public import CORALean.Specification.SyntaxTree.Operations.Interval

@[expose] public section

/-!
# `aux_exp_`: the contraction of `exp`

`aux_exp_(int,intPrev)` of `syntaxTree.m`: `log` of `int` cut to the positive reals, met with
`intPrev`;
`log(0) = -Inf`. An `int` below `0` throws `CORA:outOfDomain`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `aux_exp_`: `log(int)` cut to the positive reals, met with `intPrev`. -/
noncomputable def SyntaxTree.funHanExp (int prev : Dom) : Outcome Dom :=
  let step := fun (int : Dom) =>
    -- `log(0) = -Inf`
    let temp₁ : EReal := if int.inf 0 = 0 then ⊥ else (Real.log (int.inf 0) : ℝ)
    let temp₂ : EReal := if int.sup 0 = 0 then ⊥ else (Real.log (int.sup 0) : ℝ)
    Outcome.ok (restrict prev (min temp₁ temp₂) (max temp₁ temp₂))
  if int.inf 0 < 0 then
    if int.sup 0 < 0 then .outOfDomain else step (interval 0 (int.sup 0))
  else step int

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
