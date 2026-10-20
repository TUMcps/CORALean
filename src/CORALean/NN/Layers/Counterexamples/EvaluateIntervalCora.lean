module

public import CORALean.ContSet.Interval.Real.Interval
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# `Layer.evaluateIntervalCora`: `evaluateInterval` of a layer as CORA's code runs

The default `evaluateInterval` of `nnLayer.m` (l. 141-144), inherited by `nnSquareLayer`,
`nnActLayerFromHandle` and `nnSoftmaxLayer`, evaluates the layer function at the two end points and
returns the results as the new bounds. That is the image only for a function increasing on the box.
Read from the source, not run.

`evaluate(nnSquareLayer, interval(-1,2))` is `interval(1,4)`, while `x^2` takes the value `0` at `x
= 0 ∈ [-1,2]`: the enclosure is not one. The same holds for `sin` on `interval(0,3)`.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the result is `[1, 4]` and some point's image lies below its lower bound
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
