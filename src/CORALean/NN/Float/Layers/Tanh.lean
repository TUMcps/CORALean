import CORALean.NN.Float.Layers.Sigmoid
import CORALean.NN.Layers.Tanh

/-!
# The tanh layer over a floating-point scalar

`tanh t = 2 σ(2t) - 1`, taken literally: the sigmoid enclosure is reused and no
second exponential enclosure exists. That is why this file imports the sigmoid
layer rather than `Global/Float` directly.

The only new step is doubling the argument, and it is free. `addDown a a` and
`addUp a a` bracket `2t`, and `σ` is monotone, so each direction's rounding
pushes `σ(2t)` the way that direction needs — no bound on the doubling's error
is required anywhere.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open ContSet FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]

/-- Clearing `e⁻ᵗ` from both sides of `tanh` leaves `(1 - e⁻²ᵗ)/(1 + e⁻²ᵗ)`,
which is `2 σ(2t) - 1`. -/
private theorem tanh_eq_sigmoid (t : ℝ) : Real.tanh t = 2 * Real.sigmoid (2 * t) - 1 := by
  have hpos : (0:ℝ) < Real.exp t := Real.exp_pos t
  have hE : Real.exp t ≠ 0 := ne_of_gt hpos
  have h1 : Real.exp (-t) = (Real.exp t)⁻¹ := Real.exp_neg t
  have h2 : Real.exp (-(2 * t)) = (Real.exp t * Real.exp t)⁻¹ := by
    rw [Real.exp_neg, two_mul, Real.exp_add]
  have hA : Real.exp t + (Real.exp t)⁻¹ ≠ 0 := by positivity
  have hB : (1:ℝ) + (Real.exp t * Real.exp t)⁻¹ ≠ 0 := by positivity
  rw [Real.tanh_eq, Real.sigmoid, h1, h2]
  field_simp
  ring

/-- A sigmoid enclosure is a tanh one. -/
def Enclosure.tanhOfSigmoid (E : Enclosure 𝕋 Real.sigmoid) : Enclosure 𝕋 Real.tanh where
  lo a := subDown (addDown (E.lo (addDown a a)) (E.lo (addDown a a))) one
  hi a := subUp (addUp (E.hi (addUp a a)) (E.hi (addUp a a))) one
  lo_le a := by
    have hd : toReal (addDown a a) ≤ 2 * toReal a := by
      linarith [addDown_le_add a a]
    have hmono := Real.sigmoid_mono hd
    have hlo := E.lo_le (addDown a a)
    have hadd := addDown_le_add (E.lo (addDown a a)) (E.lo (addDown a a))
    have hsub := subDown_le_sub (addDown (E.lo (addDown a a)) (E.lo (addDown a a))) one
    rw [toReal_one] at hsub
    rw [tanh_eq_sigmoid (toReal a)]
    linarith
  -- the doubling rounds the same way as the bound it feeds, so the direction survives
  le_hi a := by
    have hd : 2 * toReal a ≤ toReal (addUp a a) := by
      linarith [add_le_addUp a a]
    have hmono := Real.sigmoid_mono hd
    have hhi := E.le_hi (addUp a a)
    have hadd := add_le_addUp (E.hi (addUp a a)) (E.hi (addUp a a))
    have hsub := sub_le_subUp (addUp (E.hi (addUp a a)) (E.hi (addUp a a))) one
    rw [toReal_one] at hsub
    rw [tanh_eq_sigmoid (toReal a)]
    linarith

def tanhEnclosure (k : ℕ) : Enclosure 𝕋 Real.tanh := (sigmoidEnclosure k).tanhOfSigmoid

namespace Layer

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [IntervalOuter S 𝕋] [OfInterval S 𝕋] {n : ℕ}

noncomputable def tanh (k : ℕ) : Real.Layer S n n :=
  Layer.activation (Relaxation.ofMonotone Real.tanh_mono (tanhEnclosure k))

end Layer

end CORALean.Float
