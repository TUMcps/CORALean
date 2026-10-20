module

public import CORALean.ContSet.Interval.Real.Interval
public import Mathlib.Analysis.SpecialFunctions.Exp

@[expose] public section

/-!
# `Layer.expMinMaxDiffOrderCora`: the error bound of `nnExpLayer` as CORA's code runs

`nnHelper.minMaxDiffOrder` asks the layer for the bounds of its derivative with two outputs,
`[der1l,der1u] = layer.getDerBounds(l, u)`, while `nnExpLayer.getDerBounds` is declared with one
output, `der1 = interval(exp(l), exp(u))`, so MATLAB stops with `Too many output arguments`.
`nnExpLayer` sets no `monotonicity`, so the other branch is not taken. Reached by
`nnExpLayer().evaluate(zonotope(0,1))`; `none` is the MATLAB error. Read from the source, not run.

For `l < u` the derivative is enclosed by `[exp l, exp u]`, but the caller expects two return values
and gets one: the exponential layer's error bound is never computed.

## Inputs
* `l` – lower end of the interval
* `u` – upper end of the interval

## Hypotheses
* none

## Conclusion
* the error bound is an error while the derivative bounds enclose the derivative
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
