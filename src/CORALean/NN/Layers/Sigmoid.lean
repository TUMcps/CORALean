import CORALean.NN.Layers.Activation

/-!
# The sigmoid layer

CORA's `nnSigmoidLayer`, defined here because Mathlib has no logistic function
and stated as `(1 + e⁻ᵗ)⁻¹` so that monotonicity is the denominator's.

The relaxation is the monotone one, with slope zero: the output range is
`[σ(l), σ(u)]`, which is what monotonicity alone certifies — the range of
`σ t - λ t` over the box only widens as `λ` leaves zero.

A slope that pays off needs curvature: sigmoid is convex below zero and concave
above it, so on one side the secant bounds it as convexity bounds ReLU, and the
other then needs a derivative bound this layer does not have.

`Float.Layer.sigmoid` is this relaxation again: `Float.Relaxation.ofMonotone`
asks only for `σ` at the two ends, and `Float.sigmoidEnclosure` supplies it from
`expDown` and a division. Stating `σ` as `1 - 1/(1 + eᵗ)` below and `1/(1 + e⁻ᵗ)`
above leaves both directions needing a *lower* bound on an exponential, the
direction that holds at every argument, so that enclosure carries no hypothesis.
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
