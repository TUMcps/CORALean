module

public import CORALean.ContSet.Interval.Real.Interval
public import Mathlib.Analysis.SpecialFunctions.Exp

@[expose] public section

/-!
# `Layer.expMinMaxDiffOrderCora`: the error bound of `nnExpLayer` as CORA's code runs

`nnHelper.minMaxDiffOrder` (the error bound of every activation layer without a `monotonicity`)
asks the layer for the bounds of its derivative with two outputs,

```
[der1l,der1u] = layer.getDerBounds(l, u);
```

(the abstract method of `nnActivationLayer` is `[df_l,df_u] = getDerBounds(obj, l, u)`), while
`nnExpLayer.getDerBounds` is declared with one output,

```
function der1 = getDerBounds(obj, l, u)
    der1 = interval(exp(l), exp(u));
```

so MATLAB stops with `Too many output arguments`. `nnExpLayer` sets no `monotonicity`, and the
other branch of `minMaxDiffOrder` is not taken. Reached by `nnExpLayer().evaluate(zonotope(0,1))`
(`computeApproxPoly` with `'regression'`, the default, or `'bounds'`, the training default;
`'singh'` computes `d` itself and does not get there). `none` is the MATLAB error. Read from the
source, not run.

# CORA's `nnExpLayer` stops on every interval of positive width

For `l < u` the derivative `exp` of `exp` is enclosed by `[exp l, exp u]`, which is what
`getDerBounds` computes, but the caller expects two return values and gets one: the error
bound of the exponential layer is never computed. Read from the source, not run.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- The model: CORA's code as printed, kept only to be refuted.
/-- The single return value of `nnExpLayer.getDerBounds`: `interval(exp(l), exp(u))`. -/
noncomputable def Layer.expGetDerBoundsCora (l u : ℝ) : Interval ℝ :=
  ⟨Real.exp l, Real.exp u⟩

/-- `minMaxDiffOrder`'s call `[der1l,der1u] = layer.getDerBounds(l, u)` for the exponential
layer: `none` is the MATLAB error `Too many output arguments`, the callee having one output. -/
def Layer.expMinMaxDiffOrderCora (_l _u : ℝ) : Option (Interval ℝ) :=
  none

end CORALean.Real

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- The bound of the exponential layer's error stops with an error for every `l`, `u`, although
`[exp l, exp u]` encloses the derivative on `[l, u]`. -/
theorem Layer.exp_cora_crash (l u : ℝ) :
    Layer.expMinMaxDiffOrderCora l u = none ∧
      ∀ x ∈ Set.Icc l u, Real.exp x ∈ Set.Icc (Layer.expGetDerBoundsCora l u).inf
        (Layer.expGetDerBoundsCora l u).sup := by
  refine ⟨rfl, fun x hx => ?_⟩
  exact ⟨Real.exp_le_exp.2 hx.1, Real.exp_le_exp.2 hx.2⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
