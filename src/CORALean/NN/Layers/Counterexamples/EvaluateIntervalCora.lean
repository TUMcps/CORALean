module

public import CORALean.ContSet.Interval.Real.Interval
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# `Layer.evaluateIntervalCora`: `evaluateInterval` of a layer as CORA's code runs

`nn/layers/nnLayer.m`, the default `evaluateInterval` (l. 141-144), which `nnSquareLayer`,
`nnActLayerFromHandle` and `nnSoftmaxLayer` inherit (no `evaluateInterval` is defined for them;
`nnActivationLayer.evaluateInterval` only updates the stored bounds and calls it):

```
bounds = obj.evaluateNumeric(cat(3,bounds.inf,bounds.sup), options);
bounds = interval(bounds(:,:,1),bounds(:,:,2));
```

The layer function is evaluated at the two end points and the results are the new bounds. That is
the image only for a function that is increasing on the box. `neuralNetwork/evaluate` with an
`interval` input reaches it layer by layer (`evaluate_.m`, `aux_evaluateInterval`). One neuron;
the `interval` constructor's error for lower above upper (a decreasing function, `cos` on
`[0, 4]`; tolerance `1e-6`) is not modelled. Read from the source, not run.

# CORA's `evaluateInterval` of `nnSquareLayer` misses the minimum

`nnSquareLayer` has `evaluateNumeric(x) = x.^2`, so `evaluate(nnSquareLayer, interval(-1,2))` is
`interval(1,4)`, while `x^2` takes the value `0` at `x = 0 ∈ [-1,2]`: the enclosure is not one.
The same holds for `sin` on `interval(0,3)` (`[0, 0.1411]` against `[0, 1]`). Read from the
source, not run.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- The model: CORA's code as printed, kept only to be refuted.
/-- CORA's `evaluateInterval` of a layer with the elementwise function `f`, on `[lo, hi]`:
`interval(f(inf), f(sup))`. -/
def Layer.evaluateIntervalCora (f : ℝ → ℝ) (lo hi : ℝ) : Interval ℝ :=
  ⟨f lo, f hi⟩

end CORALean.Real

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- `nnSquareLayer` (`f x = x ^ 2`) on `interval(-1,2)`: CORA returns `[1, 4]`, and the point
`0 ∈ [-1,2]` has the image `0`, below the lower bound. -/
theorem Layer.evaluateInterval_cora_counterexample :
    Layer.evaluateIntervalCora (fun x => x ^ 2) (-1) 2 = ⟨1, 4⟩ ∧
      ∃ x ∈ Set.Icc (-1 : ℝ) 2,
        x ^ 2 < (Layer.evaluateIntervalCora (fun x => x ^ 2) (-1) 2).inf := by
  refine ⟨by simp [Layer.evaluateIntervalCora]; norm_num, 0, ⟨by norm_num, by norm_num⟩, ?_⟩
  simp [Layer.evaluateIntervalCora]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
