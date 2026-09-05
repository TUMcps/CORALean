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

`tanh' t = (1 + tanh t)(1 - tanh t)` is a product of two positive monotone
factors, as sigmoid's derivative is, so the enclosure at the box's ends brackets
it the same way and `Relaxation.ofDeriv` reads a slope off it. The lower factors
are floored at zero: `tanh` stays inside `(-1, 1)` but a rounded bound on it
need not.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Float

open ContSet FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]

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
    rw [Real.tanh_eq_sigmoid (toReal a)]
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
    rw [Real.tanh_eq_sigmoid (toReal a)]
    linarith

def tanhEnclosure (k : ℕ) : Enclosure 𝕋 Real.tanh := (sigmoidEnclosure k).tanhOfSigmoid

/-! ## The derivative bracket

`1 + tanh` is largest at the box's right end and `1 - tanh` at its left, and
both stay positive — but only the exact values do, so the two lower factors are
floored at zero before they are multiplied. -/

def tanhDerivLo (E : Enclosure 𝕋 Real.tanh) (l u : 𝕋) : 𝕋 :=
  mulDown (maximum zero (addDown one (E.lo l))) (maximum zero (subDown one (E.hi u)))

def tanhDerivHi (E : Enclosure 𝕋 Real.tanh) (l u : 𝕋) : 𝕋 :=
  mulUp (addUp one (E.hi u)) (subUp one (E.lo l))

theorem tanhDerivLo_le (E : Enclosure 𝕋 Real.tanh) (l u : 𝕋) (x : ℝ)
    (hl : toReal l ≤ x) (hu : x ≤ toReal u) :
    toReal (tanhDerivLo E l u) ≤ Real.tanhDeriv x := by
  have h₁ : toReal (maximum zero (addDown one (E.lo l))) ≤ 1 + Real.tanh x := by
    rw [toReal_maximum, toReal_zero]
    refine max_le (by linarith [Real.neg_one_lt_tanh x]) ?_
    have ha := addDown_le_add (one : 𝕋) (E.lo l)
    have hb := le_trans (E.lo_le l) (Real.tanh_mono hl)
    rw [toReal_one] at ha
    linarith
  -- the mirrored factor: an upper bound on `tanh` at the right end is a lower one here
  have h₂ : toReal (maximum zero (subDown one (E.hi u))) ≤ 1 - Real.tanh x := by
    rw [toReal_maximum, toReal_zero]
    refine max_le (by linarith [Real.tanh_lt_one x]) ?_
    have ha := subDown_le_sub (one : 𝕋) (E.hi u)
    have hb := le_trans (Real.tanh_mono hu) (E.le_hi u)
    rw [toReal_one] at ha
    linarith
  have h₀ : 0 ≤ toReal (maximum zero (subDown one (E.hi u))) := by
    rw [toReal_maximum, toReal_zero]
    exact le_max_left _ _
  rw [tanhDerivLo, Real.tanhDeriv]
  exact le_trans (mulDown_le_mul _ _)
    (mul_le_mul h₁ h₂ h₀ (by linarith [Real.neg_one_lt_tanh x]))

theorem le_tanhDerivHi (E : Enclosure 𝕋 Real.tanh) (l u : 𝕋) (x : ℝ)
    (hl : toReal l ≤ x) (hu : x ≤ toReal u) :
    Real.tanhDeriv x ≤ toReal (tanhDerivHi E l u) := by
  -- upward no floor is needed: both factors bound quantities already known positive
  have h₁ : 1 + Real.tanh x ≤ toReal (addUp one (E.hi u)) := by
    have ha := add_le_addUp (one : 𝕋) (E.hi u)
    have hb := le_trans (Real.tanh_mono hu) (E.le_hi u)
    rw [toReal_one] at ha
    linarith
  have h₂ : 1 - Real.tanh x ≤ toReal (subUp one (E.lo l)) := by
    have ha := sub_le_subUp (one : 𝕋) (E.lo l)
    have hb := le_trans (E.lo_le l) (Real.tanh_mono hl)
    rw [toReal_one] at ha
    linarith
  rw [tanhDerivHi, Real.tanhDeriv]
  exact le_trans (mul_le_mul h₁ h₂ (by linarith [Real.tanh_lt_one x])
    (by linarith [Real.neg_one_lt_tanh x])) (mul_le_mulUp _ _)

/-! ## The relaxation

As for sigmoid: the secant is a guess, and the clamp into the bracket is what
makes a zero-width box, where `divUp` bounds nothing, harmless. -/

def tanhSlope (E : Enclosure 𝕋 Real.tanh) (l u : 𝕋) : 𝕋 :=
  maximum (tanhDerivLo E l u)
    (minimum (tanhDerivHi E l u) (divUp (subUp (E.hi u) (E.lo l)) (subDown u l)))

noncomputable def tanhCurvatureRelaxation (E : Enclosure 𝕋 Real.tanh) :
    Relaxation 𝕋 Real.tanh :=
  Relaxation.ofDeriv Real.tanhDeriv Real.hasDerivAt_tanh E
    (tanhDerivLo E) (tanhDerivHi E) (tanhSlope E)
    (tanhDerivLo_le E) (le_tanhDerivHi E) fun l u h => by
      refine ⟨by rw [tanhSlope, toReal_maximum]; exact le_max_left _ _, ?_⟩
      rw [tanhSlope, toReal_maximum, toReal_minimum]
      exact max_le (le_trans (tanhDerivLo_le E l u (toReal l) le_rfl h)
        (le_tanhDerivHi E l u (toReal l) le_rfl h)) (min_le_left _ _)

namespace Layer

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [IntervalOuter S 𝕋] [OfInterval S 𝕋] {n : ℕ}

/-- `k` is the reduction depth the sigmoid enclosure underneath is built at. -/
noncomputable def tanh (k : ℕ) : Real.Layer S n n :=
  Layer.activation ((tanhCurvatureRelaxation (tanhEnclosure k)).tighter
    (Relaxation.ofMonotone Real.tanh_mono (tanhEnclosure k)))

end Layer

end CORALean.Float
