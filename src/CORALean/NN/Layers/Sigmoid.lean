import CORALean.NN.Layers.Activation

/-!
# The sigmoid layer

CORA's `nnSigmoidLayer`. Defined here rather than taken from Mathlib, which has
no logistic function, and stated as `(1 + e⁻ᵗ)⁻¹` so that monotonicity is the
denominator's and nothing more.

The relaxation is the monotone one, with slope zero: the neuron's output range
is `[σ(l), σ(u)]` and that is all the enclosure claims. That is not a placeholder
but what monotonicity alone certifies — for a monotone `σ` the range of
`σ t - λ t` over the box only widens as `λ` leaves zero, so no other slope is an
improvement on this evidence.

A slope that does pay off needs curvature: sigmoid is convex below zero and
concave above it, and on one side of the origin the secant bounds it from one
side exactly as convexity bounds ReLU. The other side then needs the tangent,
hence a derivative bound, which is a piece of analysis this layer does not yet
have. The `Relaxation` field is where it would go, and nothing else would
change.

The float counterpart is `Float.Layer.sigmoid`, and it is this relaxation
again: `Float.Relaxation.ofMonotone` asks only for `σ` at the two ends of a
neuron's range, and `Float.sigmoidEnclosure` supplies it from `Global/Float`'s
directed `expDown` and a division. Stating `σ` as `1 - 1/(1 + eᵗ)` for the lower
end and `1/(1 + e⁻ᵗ)` for the upper leaves both directions needing a *lower*
bound on an exponential, which is the direction that holds at every argument —
so that enclosure carries no hypothesis.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix ContSet

noncomputable def sigmoid (t : ℝ) : ℝ := (1 + Real.exp (-t))⁻¹

theorem sigmoid_mono : Monotone sigmoid := by
  intro a b hab
  have hpb : (0:ℝ) < 1 + Real.exp (-b) := by positivity
  have hexp : Real.exp (-b) ≤ Real.exp (-a) := Real.exp_le_exp.mpr (by linarith)
  show (1 + Real.exp (-a))⁻¹ ≤ (1 + Real.exp (-b))⁻¹
  rw [inv_eq_one_div, inv_eq_one_div]
  exact one_div_le_one_div_of_le hpb (by linarith)

noncomputable def sigmoidRelaxation : Relaxation sigmoid :=
  Relaxation.ofMonotone sigmoid_mono

namespace Layer

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat ℝ) S] [IntervalOuter S] [OfInterval S] {n : ℕ}

noncomputable def sigmoid : Layer S n n := Layer.activation sigmoidRelaxation

end Layer

end CORALean.Real
