import CORALean.NN.Layers.Activation

/-!
# The tanh layer

CORA's `nnTanhLayer`, over Mathlib's `Real.tanh`, which has no monotonicity
lemma; `tanh_mono` supplies one by clearing the two denominators, where what
is left is `e^{b-a} ≥ e^{a-b}`.

The relaxation is the monotone one, with slope zero, for the same reason as
sigmoid: monotonicity alone certifies the output range and no slope beyond it.
Tanh is a rescaled sigmoid, so a curvature-based relaxation would carry over to
both at once.

The float counterpart is `Float.Layer.tanh`, and it takes the rescaling
literally: `tanh t = 2 σ(2t) - 1`, so `Float.sigmoidEnclosure` is reused rather
than a second exponential enclosure written. Only the doubled argument is new,
and it rounds outward in whichever direction is being bounded, which
monotonicity then carries into `σ`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix ContSet

/-- Both denominators are positive, so the claim is `e^{a-b} ≤ e^{b-a}`. -/
theorem tanh_mono : Monotone Real.tanh := by
  intro a b hab
  rw [Real.tanh_eq, Real.tanh_eq, div_le_div_iff₀ (by positivity) (by positivity)]
  have h₁ : Real.exp a * Real.exp (-b) = Real.exp (a - b) := by
    rw [← Real.exp_add, sub_eq_add_neg]
  have h₂ : Real.exp b * Real.exp (-a) = Real.exp (b - a) := by
    rw [← Real.exp_add, sub_eq_add_neg]
  have key : Real.exp (a - b) ≤ Real.exp (b - a) := Real.exp_le_exp.mpr (by linarith)
  linarith

noncomputable def tanhRelaxation : Relaxation Real.tanh :=
  Relaxation.ofMonotone tanh_mono

namespace Layer

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat ℝ) S] [IntervalOuter S] [OfInterval S] {n : ℕ}

noncomputable def tanh : Layer S n n := Layer.activation tanhRelaxation

end Layer

end CORALean.Real
