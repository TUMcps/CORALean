module

public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# `Layer.linearConZonotopeCenterCora`: `evaluateConZonotope` of `nnLinearLayer` as CORA's code runs

`nn/layers/linear/nnLinearLayer.m` carries an additive approximation error `d` (property `d`,
"approx error (additive)"; `neuralNetwork/computeReducedNetwork.m`, l. 228-246, sets it to
`W2*approx_error` for the merged neurons). `evaluateNumeric` samples it, `evaluateInterval` adds
it (`bounds + obj.d`, l. 111-113) and `evaluatePolyZonotope` adds `center(d)` to `c` and
`diag(rad(d))` to `GI` (l. 134-137). The two remaining set evaluations leave it out:

```
function r = evaluateTaylm(obj, input, options)
    r = obj.W * input + obj.b;
function [c, G, C, d, l, u] = evaluateConZonotope(obj, c, G, C, d, l, u, options)
    c = obj.W * c + obj.b;
    G = obj.W * G;
```

(`evaluateZonotopeBatch` does likewise.) `neuralNetwork/evaluate` takes `taylm` and `conZonotope`
inputs (`inputArgsCheck`, `evaluate_.m`), so a reduced network `nn_red` of `computeReducedNetwork`
evaluated on a `conZonotope` returns a set that omits the error. One neuron; the zonotope part
`c + G ξ`, `ξ ∈ [-1,1]`. Read from the source, not run.

# CORA's linear layer drops the approximation error for a constrained zonotope

`L = nnLinearLayer(1, 0); L.d = interval(-1,1)` maps `zonotope(0,0)` to `[-1,1]` (polynomial
zonotope path) and `interval(0,0)` to `[-1,1]`, but `conZonotope(0,0)` to the point `0`: the output
`1`, reached by `x = 0`, `e = 1 ∈ d`, is missed. Read from the source, not run.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- The model: CORA's code as printed, kept only to be refuted.
/-- The center of the output of `evaluateConZonotope`, one neuron: `c = W c + b`; the error `d`
is not read. -/
def Layer.linearConZonotopeCenterCora (W b c : ℝ) : ℝ :=
  W * c + b

/-- The generator of the output of `evaluateConZonotope`, one neuron: `G = W G`. -/
def Layer.linearConZonotopeGeneratorCora (W G : ℝ) : ℝ :=
  W * G

end CORALean.Real

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- For `W = 1`, `b = 0`, the input `{0}` and `d = [-1, 1]`, the layer's output `1 = W 0 + b + 1`
lies outside the set `c' + G' ξ` that CORA returns. -/
theorem Layer.linearConZonotope_cora_counterexample : -- --- CONCL ---
    (∃ x e : ℝ, x ∈ Set.Icc (0 : ℝ) 0 ∧ e ∈ Set.Icc (-1 : ℝ) 1 ∧ (1 : ℝ) = 1 * x + 0 + e) ∧
      ∀ ξ ∈ Set.Icc (-1 : ℝ) 1,
        (1 : ℝ) ≠ Layer.linearConZonotopeCenterCora 1 0 0
          + Layer.linearConZonotopeGeneratorCora 1 0 * ξ := by -- --- PROOF ---
  refine ⟨⟨0, 1, by simp, by simp, by norm_num⟩, fun ξ _ => ?_⟩
  simp [Layer.linearConZonotopeCenterCora, Layer.linearConZonotopeGeneratorCora]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
