module

public import CORALean.ContSet.Interval.Real.Operations.Intersection
public import CORALean.Specification.SyntaxTree.Definitions.Basic
public import CORALean.Specification.SyntaxTree.Operations.FunHanPowerOddCora

@[expose] public section

/-!
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
