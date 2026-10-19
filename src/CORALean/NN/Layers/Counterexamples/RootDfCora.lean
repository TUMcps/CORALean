module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# `Layer.rootDfCora`: the derivative of `nnRootLayer` as CORA's code defines it

`nn/layers/nonlinear/nnRootLayer.m` (l. 41-47):

```
function df_i = getDf(obj, i)
    if i == 0
        df_i = obj.f;
    else
        df_i1 = obj.getDf(i-1);
        df_i = @(x) 1 / 2 .* df_i1(x);
```

so `getDf(1) = 1/2 * sqrt(x)`, where the derivative of `sqrt` is `1 / (2 * sqrt(x))`
(`nnInvSqrtRootLayer.getDf` has it right). The `nnActivationLayer` constructor stores it as
`obj.df`; `evaluateSensitivity`, `backpropNumeric`, `getDerBounds`, `taylor` coefficients and
the tangent of `computeApproxPoly` use it. `computeApproxPoly` with `poly_method = 'singh'` and
order 1 (`nnSShapeLayer` sets `monotonicity = 1`, the order defaults to 1) builds the DeepZ band
from it (l. 75-82):

```
lambda = min(obj.df(l), obj.df(u));
mu1 = 0.5 * (obj.f(u) + obj.f(l) - lambda * (u + l));
mu2 = 0.5 * (obj.f(u) - obj.f(l) - lambda * (u - l));
coeffs = [lambda, mu1];  d = mu2;
```

`coeffs` is the line `lambda x + mu1` and `d` the radius around it. Read from the source, not
run.

# CORA's `nnRootLayer` derivative is `sqrt(x) / 2`, and the `'singh'` band misses `sqrt`

At `x = 4` the derivative of `sqrt` is `1/4` and CORA's `df` returns `1`. On `[1/4, 9]` the slope
`lambda` is `min(1/4, 3/2) = 1/4`, but `sqrt` is concave with minimal slope `1/6` at `9`, so the
line `x/4 + 19/32` with radius `mu2 = 5/32` does not enclose `sqrt`: at `x = 4` the gap is
`2 - (1 + 19/32) = 13/32 > 5/32`. With the right `df` the slope is `1/6` and the band is sound.
Read from the source, not run.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- The model: CORA's code as printed, kept only to be refuted.
/-- `nnRootLayer.getDf(1)` as printed: `1 / 2 .* df_0(x)` with `df_0 = sqrt`. -/
noncomputable def Layer.rootDfCora (x : ℝ) : ℝ :=
  1 / 2 * Real.sqrt x

/-- The slope `lambda` of the `'singh'` transformer of `computeApproxPoly` at order 1. -/
noncomputable def Layer.singhLambdaCora (df : ℝ → ℝ) (l u : ℝ) : ℝ :=
  min (df l) (df u)

/-- Its offset `mu1`, the line being `lambda x + mu1`. -/
noncomputable def Layer.singhMu1Cora (f df : ℝ → ℝ) (l u : ℝ) : ℝ :=
  1 / 2 * (f u + f l - Layer.singhLambdaCora df l u * (u + l))

/-- Its radius `mu2`, which is `d`. -/
noncomputable def Layer.singhMu2Cora (f df : ℝ → ℝ) (l u : ℝ) : ℝ :=
  1 / 2 * (f u - f l - Layer.singhLambdaCora df l u * (u - l))

end CORALean.Real

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- CORA's `df` of `nnRootLayer` is `1` at `4`, where the derivative of `sqrt` is `1/4`, and the
`'singh'` band on `[1/4, 9]` misses `sqrt 4`. -/
theorem Layer.rootDf_cora_counterexample : -- --- CONCL ---
    Layer.rootDfCora 4 = 1 ∧ HasDerivAt Real.sqrt (1 / 4) 4 ∧
      ∃ x ∈ Set.Icc (1 / 4 : ℝ) 9,
        Layer.singhMu2Cora Real.sqrt Layer.rootDfCora (1 / 4) 9 <
          |Real.sqrt x - (Layer.singhLambdaCora Layer.rootDfCora (1 / 4) 9 * x +
            Layer.singhMu1Cora Real.sqrt Layer.rootDfCora (1 / 4) 9)| := by -- --- PROOF ---
  have s4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  have s9 : Real.sqrt 9 = 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  have s14 : Real.sqrt (1 / 4) = 1 / 2 := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  refine ⟨by simp [Layer.rootDfCora, s4], ?_, 4, ⟨by norm_num, by norm_num⟩, ?_⟩
  · have h := Real.hasDerivAt_sqrt (x := (4 : ℝ)) (by norm_num)
    rw [s4] at h
    convert h using 1
    norm_num
  · simp only [Layer.singhMu2Cora, Layer.singhMu1Cora, Layer.singhLambdaCora, Layer.rootDfCora,
      s4, s9, s14]
    norm_num [abs_of_pos]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
