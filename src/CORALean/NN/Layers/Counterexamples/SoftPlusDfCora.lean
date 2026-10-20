module

public import CORALean.NN.Layers.Definitions.Softplus
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# `Layer.softplusDfCora`: the derivative of `nnSoftPlusLayer` as CORA's code caches it

`nnSoftPlusLayer.m` declares `sharpness = 2` as the property default and reads `sharpness` from
`varargin` only *after* the superclass constructor has stored `obj.df = obj.getDf(1)`, the symbolic
derivative of `(1/k) log(1 + exp(k x))` at the default `k = 2`. `lookupDf` keeps it in a persistent
map under the class name, so every softplus layer gets the derivative of `k = 2` whatever its
`sharpness`. Read from the source, not run.

With `sharpness = 1`, `layer.df(1)` returns `0.881` instead of `exp 1 / (1 + exp 1) = 0.731`.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* CORA's derivative at one differs from the true derivative at sharpness one
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
theorem Layer.softplusDf_cora_counterexample : -- --- CONCL ---
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
