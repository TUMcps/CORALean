module

public import Mathlib.Data.Real.Basic
public import CORALean.NN.Layers.Theorems.Real.DeepZSShapeCubeNotSound

@[expose] public section

/-!
# `evaluatePolyZonotopeNeuron` with `poly_method = 'singh'`, order 1, as printed

CORA's `@nnActivationLayer/evaluatePolyZonotopeNeuron.m` bounds the neuron's input
(`aux_computeBounds`, `l`, `u`), calls `computeApproxPoly(obj, l, u, order, 'singh')` and evaluates
the returned polynomial on the polynomial zonotope. For a layer with `monotonicity` set and
`order == 1` the `'singh'` branch of `computeApproxPoly.m` is [1, Thm. 3.2] for every activation,
with `df` the layer's derivative:

```
lambda = min(obj.df(l), obj.df(u));
mu1 = 0.5 * (obj.f(u) + obj.f(l) - lambda * (u + l));
mu2 = 0.5 * (obj.f(u) - obj.f(l) - lambda * (u - l));
coeffs = [lambda, mu1];
d = mu2;
```

The input is a zonotope `c + g ε`, so `[l, u] = [c - |g|, c + |g|]`; the output is
`(lambda c + mu1, lambda g, d)`, `d` the error `aux_addApproxError` adds as a generator.

# A two-neuron network through CORA's `'singh'` neuron step

`neuralNetwork.evaluate` with `options.nn.poly_method = 'singh'` on a zonotope: the linear layer
`x ↦ (a₁ x + b₁, a₂ x + b₂)`, the activation layer `nnActLayerFromHandle(f, [], 1)` whose
neurons each run `NN.evaluateSinghNeuronCora`, and the linear layer `(z₁, z₂) ↦ z₁ + z₂`. The
two neurons share the input generator, which the second linear layer adds up, and each carries
its error as a fresh generator. The result is the interval `center ± (|generator| + |d₁| + |d₂|)`
of the output zonotope.

A single neuron cannot show a miss: for a monotone `f` the band is exact at both ends of the
interval. The shared generator is what makes the error of one neuron visible.

# CORA's `'singh'` evaluation misses a true output of a network with activation `x³`

`nnActLayerFromHandle(@(x) x.^3, [], 1)` sets `monotonicity` for any handle, and
`options.nn.poly_method = 'singh'` is a documented option of `neuralNetwork/evaluate`. On the
network `x ↦ (x, 3 - x) ↦ (x³, (3 - x)³) ↦ x³ + (3 - x)³` and the input `[-1, 2]` the first neuron
gets the line `3 x + 2` with `d = 0` (`deepZSShape_cube_not_sound`), the second, on `[1, 4]`, the
line `34 - 3 x` with `d = 27`. The generators cancel, and the output is `[9, 63]`; the true output
at `x = 3/2` is `6.75`.

## References

* [1] G. Singh, T. Gehr, M. Mirman, M. Püschel and M. Vechev. "Fast and Effective Robustness
      Certification". NeurIPS 2018.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- The model: CORA's code as printed, kept only to be refuted.
/-- The neuron step on `c + g ε`: center, generator, error `d`. -/
noncomputable def NN.evaluateSinghNeuronCora (f df : ℝ → ℝ) (c g : ℝ) : ℝ × ℝ × ℝ :=
  let l := c - |g|
  let u := c + |g|
  let lambda := min (df l) (df u)
  let mu1 := 0.5 * (f u + f l - lambda * (u + l))
  let mu2 := 0.5 * (f u - f l - lambda * (u - l))
  (lambda * c + mu1, lambda * g, mu2)


-- The model: CORA's code as printed, kept only to be refuted.
/-- The output interval of the network on the input zonotope `c + g ε`. -/
noncomputable def NN.evaluateSinghCora (f df : ℝ → ℝ) (a₁ b₁ a₂ b₂ c g : ℝ) : Set ℝ :=
  let n₁ := NN.evaluateSinghNeuronCora f df (a₁ * c + b₁) (a₁ * g)
  let n₂ := NN.evaluateSinghNeuronCora f df (a₂ * c + b₂) (a₂ * g)
  {y | ∃ s e₁ e₂ : ℝ, |s| ≤ 1 ∧ |e₁| ≤ 1 ∧ |e₂| ≤ 1 ∧
    y = (n₁.1 + n₂.1) + (n₁.2.1 + n₂.2.1) * s + n₁.2.2 * e₁ + n₂.2.2 * e₂}


-- =======================================  MAIN THEOREM  ======================================= --

theorem NN.evaluateSinghCora_misses_counterexample :
    SShapedPrinted (fun x : ℝ => x ^ 3) ∧ Monotone (fun x : ℝ => x ^ 3) ∧
      ∃ x : ℝ, -1 ≤ x ∧ x ≤ 2 ∧
        x ^ 3 + (3 - x) ^ 3 ∉ NN.evaluateSinghCora (fun x : ℝ => x ^ 3)
          (deriv fun x : ℝ => x ^ 3) 1 0 (-1) 3 (1 / 2) (3 / 2) := by -- --- PROOF ---
  obtain ⟨hS, hM, -⟩ := deepZSShape_cube_not_sound
  have hd : deriv (fun x : ℝ => x ^ 3) = fun x => 3 * x ^ 2 :=
    funext fun x => by rw [(hasDerivAt_pow 3 x).deriv]; norm_num
  refine ⟨hS, hM, 3 / 2, by norm_num, by norm_num, ?_⟩
  rintro ⟨s, e₁, e₂, hs, he₁, he₂, h⟩
  simp only [NN.evaluateSinghNeuronCora, hd] at h
  norm_num [abs_of_nonneg, abs_of_nonpos, min_def] at h
  have := (abs_le.mp he₂).1
  nlinarith [h]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
