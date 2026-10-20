module

public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# `Layer.linearConZonotopeCenterCora`: `evaluateConZonotope` of `nnLinearLayer` as CORA runs it

`nnLinearLayer.m` carries an additive approximation error `d` (set by `computeReducedNetwork` for
merged neurons). `evaluateNumeric`, `evaluateInterval` and `evaluatePolyZonotope` include it; the
remaining set evaluations leave it out: `evaluateTaylm` returns `obj.W * input + obj.b` and
`evaluateConZonotope` only `c = obj.W * c + obj.b; G = obj.W * G`. So a reduced network evaluated on
a `conZonotope` returns a set that omits the error. Read from the source, not run.

`L = nnLinearLayer(1, 0); L.d = interval(-1,1)` maps `interval(0,0)` to `[-1,1]` but
`conZonotope(0,0)` to the point `0`: the output `1` is missed.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* an attainable output is not in the set CORA returns
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
