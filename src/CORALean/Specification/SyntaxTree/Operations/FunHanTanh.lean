module

public import CORALean.ContSet.Interval.Real.Operations.Intersection
public import CORALean.Specification.SyntaxTree.Operations.Interval
public import CORALean.Specification.SyntaxTree.Operations.Restrict
public import CORALean.Specification.SyntaxTree.SyntaxTree

@[expose] public section

/-!
# `aux_tanh_`: the contraction of `tanh`

`aux_tanh_(int,intPrev)` of `syntaxTree.m`: `atanh` of `int` cut to `[-1,1]` (`atanh(±1) = ±Inf`),
met
with `intPrev`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `aux_tanh_`: `atanh(int & interval(-1,1))` met with `intPrev`. -/
noncomputable def SyntaxTree.funHanTanh (int prev : Dom) : Outcome Dom :=
  -- intersection with valid domain
  let int := Real.Interval.intersection int (interval (-1) 1)
  -- apply inverse function, `atanh(±1) = ±Inf`
  let atanhE := fun (x : ℝ) =>
    (if x = -1 then ⊥ else if x = 1 then ⊤ else ↑(Real.artanh x) : EReal)
  let temp₁ := atanhE (int.inf 0)
  let temp₂ := atanhE (int.sup 0)
  .ok (restrict prev (min temp₁ temp₂) (max temp₁ temp₂))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
