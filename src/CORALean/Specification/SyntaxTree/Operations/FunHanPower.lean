module

public import CORALean.ContSet.Interval.Real.Operations.Intersection
public import CORALean.Specification.SyntaxTree.Operations.Interval
public import CORALean.Specification.SyntaxTree.Operations.Nthroot
public import CORALean.Specification.SyntaxTree.Operations.SignedRoots
public import CORALean.Specification.SyntaxTree.SyntaxTree

@[expose] public section

/-!
# `aux_power_`: the contraction of a power

`aux_power_(int,exp,intPrev)` of `syntaxTree.m` for a natural exponent: the `exp`-th root of `int`,
with
the sign of `intPrev` chosen for an even exponent (`[-m, m]` when `intPrev` contains `0`), met with
`intPrev`. Negative and fractional exponents are not modelled; `exp = 0` returns `intPrev`. The
`CORA:outOfDomain` error is `Outcome.outOfDomain`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `aux_power_`: the `k`-th root of `int` with the sign `intPrev` allows, met with `intPrev`. -/
noncomputable def SyntaxTree.funHanPower (k : ℕ) (int prev : Dom) : Outcome Dom :=
  if k = 0 then .ok prev
  else if k % 2 = 0 then
    -- even exponent: the argument has to be able to be nonnegative
    let step := fun (int : Dom) =>
      let temp₁ := nthroot (int.inf 0) k
      let temp₂ := nthroot (int.sup 0) k
      Outcome.ok (Real.Interval.intersection prev (signedRoots prev temp₁ temp₂))
    if int.inf 0 < 0 then
      if int.sup 0 < 0 then .outOfDomain else step (interval 0 (int.sup 0))
    else step int
  else
    let temp₁ := nthroot (int.inf 0) k
    let temp₂ := nthroot (int.sup 0) k
    .ok (Real.Interval.intersection prev (interval (min temp₁ temp₂) (max temp₁ temp₂)))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
