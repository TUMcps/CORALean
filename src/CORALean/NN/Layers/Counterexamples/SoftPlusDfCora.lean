module

public import CORALean.NN.Layers.Definitions.Softplus
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# `Layer.softplusDfCora`: the derivative of `nnSoftPlusLayer` as CORA's code caches it

`nn/layers/nonlinear/nnSoftPlusLayer.m` declares `sharpness = 2` as the property default and its
constructor reads

```
[sharpness,name] = setDefaultValues({1, []}, varargin);
obj@nnActivationLayer(name)
obj.sharpness = sharpness;
```

The superclass constructor runs first and stores `obj.df = obj.getDf(1)`, which is
`nnHelper.lookupDf(obj,1)`: the symbolic derivative of `obj.f(x) = (1/k).*log(1 + exp(k*x))`,
with `k = obj.sharpness`, which at that moment is the property default `2`. `lookupDf` keeps
the derivative in a persistent map under `layer.layerid`, which is the class name
(`nnLayer.m`, l. 68), so every softplus layer of the session gets the derivative of the layer
with `k = 2`, `exp(2x)/(1 + exp(2x))`, whatever its `sharpness`. `getDerBounds`, which calls
`obj.getDf(1)`, `evaluateSensitivity`, `backpropNumeric` (the training gradient), the Taylor
coefficients and the tangent of `computeApproxPoly` use it. Read from the source, not run.

# CORA's `nnSoftPlusLayer` has the derivative of the layer with `sharpness = 2`

`nnSoftPlusLayer()` (`sharpness = 1`, the constructor default) is `log(1 + exp x)` with the
derivative `exp x / (1 + exp x)`, and `layer.df(1)` returns `exp 2 / (1 + exp 2)` instead of
`exp 1 / (1 + exp 1)`: `0.881` against `0.731`. Read from the source, not run.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- The model: CORA's code as printed, kept only to be refuted.
/-- `obj.df` of a softplus layer of sharpness `_k`: the derivative of the layer with the property
default `k = 2`, stored under the class name before `sharpness` is assigned. -/
noncomputable def Layer.softplusDfCora (_k x : ℝ) : ℝ :=
  Real.exp (2 * x) / (1 + Real.exp (2 * x))

end CORALean.Real

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- At sharpness `1` the derivative of the activation at `1` is `exp 1 / (1 + exp 1)`, and CORA's
`df` returns another value. -/
theorem Layer.softplusDf_cora_counterexample :
    HasDerivAt (softplus 1) (Real.exp 1 / (1 + Real.exp 1)) 1 ∧
      Layer.softplusDfCora 1 1 ≠ Real.exp 1 / (1 + Real.exp 1) := by -- --- PROOF ---
  have he : 1 < Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  refine ⟨?_, fun h => ?_⟩
  · have h1 : HasDerivAt (fun x : ℝ => 1 * x) 1 1 := by
      simpa using (hasDerivAt_id (1 : ℝ)).const_mul 1
    have h2 := ((h1.exp).const_add 1).log (by positivity)
    have h3 := h2.const_mul (1 / (1 : ℝ))
    have h4 : softplus 1 = fun y => 1 / (1 : ℝ) * Real.log (1 + Real.exp (1 * y)) := by
      funext y; simp [softplus]
    rw [h4]
    refine h3.congr_deriv ?_
    norm_num
  · simp only [Layer.softplusDfCora, mul_one] at h
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [h2] at h
    have hpos : 0 < Real.exp 1 := by positivity
    field_simp at h
    nlinarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
