module

public import CORALean.ContSet.Interval.Real.Operations.Intersection
public import CORALean.Specification.SyntaxTree.Operations.Interval
public import CORALean.Specification.SyntaxTree.Operations.NthrootZ
public import CORALean.Specification.SyntaxTree.SyntaxTree
public import CORALean.Specification.SyntaxTree.Definitions.Basic

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

# CORA's `aux_power_` loses a solution for a negative odd exponent

For `x^(-1) - y = 0` over `[-2,2] × [-1,2]` (`syntaxTree(x)^(-1) - syntaxTree(y)`), the forward
value of `x^(-1)` is `1 ./ [-2,2] = [-Inf,Inf]`, so the target handed to `aux_power_` is
`int = [-Inf,Inf] & ([0,0] + [-1,2]) = [-1,2]` with `intPrev = [-2,2]`. The odd branch computes
`nthroot(-1,-1) = -1` and `nthroot(2,-1) = 1/2`, so `res = [-1,1/2]`: the zero `(1,1)` is lost,
since `1^(-1) = 1 ∈ [-1,2]`. The statement is about the `funHan`, as the real layer holds no
infinite bound for the forward value `[-Inf,Inf]` of the node. For a nonnegative exponent and for a
negative even exponent the same function keeps every solution (sampled on the MATLAB lines, not
proved).
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
  let temp₁ := nthrootZ (int.inf 0) e
  let temp₂ := nthrootZ (int.sup 0) e
  -- intersect with previous value
  .ok (Real.Interval.intersection prev (interval (min temp₁ temp₂) (max temp₁ temp₂)))


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
