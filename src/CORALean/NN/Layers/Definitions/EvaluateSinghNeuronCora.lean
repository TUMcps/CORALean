module

public import Mathlib.Data.Real.Basic

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


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The neuron step on `c + g ε`: center, generator, error `d`. -/
noncomputable def NN.evaluateSinghNeuronCora (f df : ℝ → ℝ) (c g : ℝ) : ℝ × ℝ × ℝ :=
  let l := c - |g|
  let u := c + |g|
  let lambda := min (df l) (df u)
  let mu1 := 0.5 * (f u + f l - lambda * (u + l))
  let mu2 := 0.5 * (f u - f l - lambda * (u - l))
  (lambda * c + mu1, lambda * g, mu2)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
