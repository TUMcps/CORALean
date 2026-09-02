import CORALean.Global.Float.Exp
import CORALean.NN.Float.Layers.Activation
import CORALean.NN.Layers.Sigmoid

/-!
# The sigmoid layer over a floating-point scalar

The relaxation is the exact layer's, `Relaxation.ofMonotone`, and all it wanted
was `σ` at the two ends of a neuron's range. `sigmoidEnclosure` is that value,
and the only new thing under it is `Global/Float`'s `expDown` and the division
that a logistic function is.

The enclosure is total — no hypothesis on the argument — and that is a choice of
*which* identity to compute each side from. `expUp` needs its argument bounded
and `expDown` does not, so both directions are written to use `expDown` alone:

* `σ t = 1 / (1 + e⁻ᵗ) ≤ 1 / D` for any `0 < D ≤ 1 + e⁻ᵗ`, the upper bound;
* `σ t = 1 - 1 / (1 + eᵗ) ≥ 1 - 1 / D` for any such `D` at `+t`, the lower one.

Each asks only that the denominator be underestimated, which is what a lower
bound on an exponential gives. `onePlusExpDown` is that denominator, held at or
above one by an exact `maximum` — a lower bound on `exp` is never negative, so
`1 + expDown a` is never below one either, and the division never meets a
divisor `SoundFloatArithmetic` says nothing about.

`k` is the exponential's reduction depth, so it is precision and nothing else:
every `k` is sound and a larger one is tighter.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open ContSet FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]

/-- `1 + exp a` from below, never below one. -/
private def onePlusExpDown (k : ℕ) (a : 𝕋) : 𝕋 := maximum one (addDown one (expDown k a))

private theorem one_le_onePlusExpDown (k : ℕ) (a : 𝕋) : 1 ≤ toReal (onePlusExpDown k a) := by
  rw [onePlusExpDown, toReal_maximum, toReal_one]
  exact le_max_left _ _

private theorem onePlusExpDown_le (k : ℕ) (a : 𝕋) :
    toReal (onePlusExpDown k a) ≤ 1 + Real.exp (toReal a) := by
  rw [onePlusExpDown, toReal_maximum]
  refine max_le ?_ (le_trans (addDown_le_add one (expDown k a)) ?_)
  · rw [toReal_one]
    linarith [Real.exp_pos (toReal a)]
  · rw [toReal_one]
    linarith [expDown_le k a]

/-- An underestimated positive denominator gives an overestimated reciprocal,
and the rounding only grows it further. -/
private theorem one_div_le_divUp {d : 𝕋} {y : ℝ} (h1 : 1 ≤ toReal d) (h2 : toReal d ≤ y) :
    1 / y ≤ toReal (divUp one d) := by
  have hd : (0:ℝ) < toReal d := lt_of_lt_of_le zero_lt_one h1
  have hdiv := div_le_divUp one d hd
  rw [toReal_one] at hdiv
  exact le_trans (one_div_le_one_div_of_le hd h2) hdiv

/-- `σ` written so that only a *lower* bound on `exp` is needed: `1/(1 + e⁻ᵗ)`
would ask for an upper one, which no total float expression supplies. -/
private theorem sigmoid_eq (t : ℝ) : Real.sigmoid t = 1 - (1 + Real.exp t)⁻¹ := by
  have hpos : (0:ℝ) < Real.exp t := Real.exp_pos t
  have hE : Real.exp t ≠ 0 := ne_of_gt hpos
  have h1 : (1:ℝ) + Real.exp t ≠ 0 := by positivity
  have h2 : (1:ℝ) + (Real.exp t)⁻¹ ≠ 0 := by positivity
  rw [Real.sigmoid, Real.exp_neg]
  field_simp
  ring

def sigmoidEnclosure (k : ℕ) : Enclosure 𝕋 Real.sigmoid where
  lo a := subDown one (divUp one (onePlusExpDown k a))
  hi a := divUp one (onePlusExpDown k (neg a))
  lo_le a := by
    have hb := one_div_le_divUp (one_le_onePlusExpDown k a) (onePlusExpDown_le k a)
    have hs := subDown_le_sub one (divUp one (onePlusExpDown k a))
    rw [toReal_one] at hs
    rw [sigmoid_eq (toReal a), ← one_div]
    linarith
  le_hi a := by
    have hb := one_div_le_divUp (one_le_onePlusExpDown k (neg a)) (onePlusExpDown_le k (neg a))
    rw [toReal_neg] at hb
    rw [Real.sigmoid, ← one_div]
    exact hb

namespace Layer

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [IntervalOuter S 𝕋] [OfInterval S 𝕋] {n : ℕ}

noncomputable def sigmoid (k : ℕ) : Real.Layer S n n :=
  Layer.activation (Relaxation.ofMonotone Real.sigmoid_mono (sigmoidEnclosure k))

end Layer

end CORALean.Float
