module

public import CORALean.ContSet.Interval.Real.Operations.Intersection
public import CORALean.Specification.SyntaxTree.Operations.Interval
public import CORALean.Specification.SyntaxTree.Operations.NthrootZ
public import CORALean.Specification.SyntaxTree.SyntaxTree
public import CORALean.Specification.SyntaxTree.Definitions.Basic

@[expose] public section

/-!
# `aux_power_` for an odd integer exponent, as printed

`aux_power_(int,exp,intPrev)` of `syntaxTree.m` handles an odd `exp` by `interval(min(temp1,temp2),
max(temp1,temp2))` with `temp1 = nthroot(infimum(int),exp)`, `temp2 = nthroot(supremum(int),exp)`,
met with `intPrev`. For `exp > 0` this is exact; for `exp < 0` and a target with `0` in its
interior the solutions are two rays and the printed interval is the gap between them.
The real layer has no infinite bounds, so `SyntaxTree.nthrootZ x e` takes `0` where CORA has `Inf`;
the model is faithful when neither bound of `int` is `0`, as in the counterexample.

# CORA's `aux_power_` loses a solution for a negative odd exponent

For `x^(-1) - y = 0` over `[-2,2] × [-1,2]` the target is `int = [-1,2]` with `intPrev = [-2,2]`;
the odd branch gives `res = [-1,1/2]`, so the zero `(1,1)` is lost. The statement is about the
`funHan`, as the real layer has no infinite forward value. Other exponents keep every solution
(sampled on the MATLAB lines, not proved).

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the printed backpropagation loses a solution of an odd negative power
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- The model: CORA's code as printed, kept only to be refuted.
/-- The odd branch of `aux_power_` as printed, for an integer exponent. -/
noncomputable def SyntaxTree.funHanPowerOddCora (e : ℤ) (int prev : Dom) : Outcome Dom :=
  -- apply inverse function
  let preInf := nthrootZ (int.inf 0) e
  let preSup := nthrootZ (int.sup 0) e
  -- intersect with previous value
  .ok (Real.Interval.intersection prev (interval (min preInf preSup) (max preInf preSup)))


-- =======================================  MAIN THEOREM  ======================================= --

/-- `aux_power_` for `exp = -1` loses `x = 1`, a solution of `x^(-1) ∈ [-1,2]` in `[-2,2]`. -/
theorem SyntaxTree.powerOddCora_counterexample :
    ∃ (int prev : Dom) (s : ℝ), Dom.contains prev s ∧ Dom.contains int (s ^ (-1 : ℤ)) ∧
      ∀ val, funHanPowerOddCora (-1) int prev = .ok val →
        ¬ Dom.contains val s := by -- --- PROOF ---
  refine ⟨interval (-1) 2, interval (-2) 2, 1, ?_, ?_, ?_⟩
  · simp [Dom.contains, interval]; norm_num
  · simp [Dom.contains, interval]
  · intro val hval
    simp [funHanPowerOddCora, nthrootZ, nthroot, Real.Interval.intersection, interval] at hval
    subst hval
    simp [Dom.contains]
    norm_num

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
