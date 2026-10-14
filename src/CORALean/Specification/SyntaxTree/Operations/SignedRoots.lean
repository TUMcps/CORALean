module

public import CORALean.Specification.SyntaxTree.SyntaxTree
public import CORALean.Specification.SyntaxTree.Operations.Interval

@[expose] public section

/-!
# The sign an operand's interval allows

In `aux_power_` (even exponent) and `aux_cosh_` the two solutions `±r` of `x² = r²` meet the
interval
`intPrev` of the operand: both if it contains `0` (`[-m, m]`), the positive one if it is
nonnegative, the
negative one otherwise. `temp₁` and `temp₂` are the roots of the two bounds of the target.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The interval of the solutions `±r` with `r` between `temp₁` and `temp₂` that `intPrev` allows.
-/
noncomputable def SyntaxTree.signedRoots (prev : Dom) (temp₁ temp₂ : ℝ) : Dom :=
  if 0 < prev.sup 0 ∧ prev.inf 0 < 0 then
    let m := max temp₁ temp₂
    interval (-m) m
  else if 0 < prev.sup 0 then interval (min temp₁ temp₂) (max temp₁ temp₂)
  else interval (-(max temp₁ temp₂)) (-(min temp₁ temp₂))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
