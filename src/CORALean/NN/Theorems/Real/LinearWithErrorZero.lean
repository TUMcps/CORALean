module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.Global.Float.Instances.Real.Instances
public import CORALean.NN.Layers.Operations.Linear
public import CORALean.NN.Layers.Operations.LinearWithError

@[expose] public section

/-!
# `Layer.linearWithError` degenerates to `Layer.linear` at ℝ

ℝ-only: the box's sum `b + 0` is exact at ℝ, where a machine scalar rounding outward on every
operation widens the point `b` to an interval, and the two layers then differ.

At `E = Interval.point 0` the committed center is `0` and the added box is a
point, so the two layers compute and enclose identically: a plain linear
layer is the error-free case of the adapted one, not a different construction.
That is [1, Eq. 2]'s initialization, `I'_k = [0, 0]`: a network adapted to carry the
error of merging denotes, before any merge, the network it was adapted from.

## Inputs
* `W` – weight matrix
* `b` – bias vector

## Hypotheses
* none

## Conclusion
* with a zero error box the layer is the plain affine layer

## References

* [1] [T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for Formal Verification".
      Transactions on Machine Learning Research,
      2025.](../../../../../references/2023/ladner-tmlr-network-reduction.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       05-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat ℝ) S] [Real.OfInterval S] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- ℝ-only, the sum `b + 0` being exact only there: at `[0, 0]` the adapted layer is the plain
one. -/
theorem Layer.linearWithError_zero (W : Mat ℝ m n) (b : Vec ℝ m) : -- --- CONCL ---
    Layer.linearWithError (S := S) W b (Float.Interval.point 0)
      = Layer.linear (S := S) W b := by -- --- PROOF ---
  -- a point box added to a point box is the point box of the sum, exactly at ℝ
  have hbox : Float.Interval.plus (Float.Interval.point b) (Float.Interval.point (0 : Vec ℝ m))
      = Float.Interval.point b := by
    show (⟨fun i => b i + 0, fun i => b i + 0⟩ : Float.Interval (Vec ℝ m)) = ⟨b, b⟩
    simp only [add_zero]
  -- a layer is its `enclose` and nothing else
  unfold Layer.linearWithError Layer.linear
  rw [hbox]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
