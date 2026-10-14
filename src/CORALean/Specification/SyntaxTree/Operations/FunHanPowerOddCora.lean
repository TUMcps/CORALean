module

public import CORALean.ContSet.Interval.Real.Operations.Intersection
public import CORALean.Specification.SyntaxTree.Operations.Interval
public import CORALean.Specification.SyntaxTree.Operations.NthrootZ
public import CORALean.Specification.SyntaxTree.SyntaxTree

@[expose] public section

/-!
# `aux_power_` for an odd integer exponent, as printed

`aux_power_(int,exp,intPrev)` of `syntaxTree.m` handles an odd `exp` by
`res = interval(min(temp1,temp2),max(temp1,temp2))`, `temp1 = nthroot(infimum(int),exp)` and
`temp2 = nthroot(supremum(int),exp)`, met with `intPrev`. For `exp > 0` the odd power is increasing
and this is exact; for `exp < 0` it is decreasing on each side of `0` and maps `x < 0` to negative
and `x > 0` to positive values. For a target `int` with `0` in its interior the solutions are two
rays, `x ≤ nthroot(infimum int,exp)` and `x ≥ nthroot(supremum int,exp)`, and the printed interval
`[temp1,temp2]` is the gap between them. `SyntaxTree.powerOddCora_counterexample` is a solution it
loses.

The real layer has no infinite bounds, so `nthroot(0,exp) = Inf` for `exp < 0` is not modelled:
`SyntaxTree.nthrootZ x e` takes the value `0` there. The model is faithful when neither bound of
`int` is `0`, which holds in the counterexample.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The odd branch of `aux_power_` as printed, for an integer exponent. -/
noncomputable def SyntaxTree.funHanPowerOddCora (e : ℤ) (int prev : Dom) : Outcome Dom :=
  -- apply inverse function
  let temp₁ := nthrootZ (int.inf 0) e
  let temp₂ := nthrootZ (int.sup 0) e
  -- intersect with previous value
  .ok (Real.Interval.intersection prev (interval (min temp₁ temp₂) (max temp₁ temp₂)))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
