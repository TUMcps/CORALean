import CORALean.Global.Float.Exp
import CORALean.NN.Float.Layers.Curvature
import CORALean.NN.Layers.Sigmoid

/-!
# The sigmoid layer over a floating-point scalar

`sigmoidEnclosure` is `σ` at a float, over `Global/Float`'s `expDown` and the
division a logistic function is. It is all the layer needs: `σ' t = σ t · σ (-t)`,
so the same enclosure at the box's ends brackets the derivative too, and the
relaxation is `Relaxation.ofDeriv` against that bracket, kept only where it beats
`Relaxation.ofMonotone`.

The enclosure is total — no hypothesis on the argument — and that is a choice of
*which* identity to compute each side from. `expUp` needs its argument bounded
and `expDown` does not, so both directions are written to use `expDown` alone:

* `σ t = 1 / (1 + e⁻ᵗ) ≤ 1 / D` for any `0 < D ≤ 1 + e⁻ᵗ`, the upper bound;
* `σ t = 1 - 1 / (1 + eᵗ) ≥ 1 - 1 / D` for any such `D` at `+t`, the lower one.

Each asks only that the denominator be underestimated, which is what a lower
bound on an exponential gives. `onePlusExpDown` is that denominator, held above
one by an exact `maximum`, so the division never meets an unconstrained divisor.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
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

/-- Both ends from `expDown`: the identity above below, `1/(1 + e⁻ᵗ)` above. -/
def sigmoidEnclosure (k : ℕ) : Enclosure 𝕋 Real.sigmoid where
  lo a := subDown one (divUp one (onePlusExpDown k a))
  hi a := divUp one (onePlusExpDown k (neg a))
  lo_le a := by
    have hb := one_div_le_divUp (one_le_onePlusExpDown k a) (onePlusExpDown_le k a)
    have hs := subDown_le_sub one (divUp one (onePlusExpDown k a))
    rw [toReal_one] at hs
    rw [sigmoid_eq (toReal a), ← one_div]
    linarith
  -- the upper end is `1/(1 + e⁻ᵗ)` directly, which is why it needs no subtraction
  le_hi a := by
    have hb := one_div_le_divUp (one_le_onePlusExpDown k (neg a)) (onePlusExpDown_le k (neg a))
    rw [toReal_neg] at hb
    rw [Real.sigmoid, ← one_div]
    exact hb

/-! ## The derivative bracket

`σ'` is a product of two sigmoids, each monotone and positive, so the enclosure
at the box's ends brackets it with no case on sign — the lower factors floored
at zero, which rounding could otherwise push below it. -/

def sigmoidDerivLo (E : Enclosure 𝕋 Real.sigmoid) (l u : 𝕋) : 𝕋 :=
  mulDown (maximum zero (E.lo l)) (maximum zero (E.lo (neg u)))

def sigmoidDerivHi (E : Enclosure 𝕋 Real.sigmoid) (l u : 𝕋) : 𝕋 :=
  mulUp (E.hi u) (E.hi (neg l))

theorem sigmoidDerivLo_le (E : Enclosure 𝕋 Real.sigmoid) (l u : 𝕋) (x : ℝ)
    (hl : toReal l ≤ x) (hu : x ≤ toReal u) :
    toReal (sigmoidDerivLo E l u) ≤ Real.sigmoidDeriv x := by
  have h₁ : toReal (maximum zero (E.lo l)) ≤ Real.sigmoid x := by
    rw [toReal_maximum, toReal_zero]
    exact max_le (le_of_lt (Real.sigmoid_pos x)) (le_trans (E.lo_le l) (Real.sigmoid_mono hl))
  have h₂ : toReal (maximum zero (E.lo (neg u))) ≤ Real.sigmoid (-x) := by
    rw [toReal_maximum, toReal_zero]
    refine max_le (le_of_lt (Real.sigmoid_pos _)) (le_trans (E.lo_le (neg u)) ?_)
    rw [toReal_neg]
    exact Real.sigmoid_mono (neg_le_neg hu)
  -- both factors are non-negative lower bounds, which is what makes the product one
  have h₀ : 0 ≤ toReal (maximum zero (E.lo (neg u))) := by
    rw [toReal_maximum, toReal_zero]
    exact le_max_left _ _
  rw [sigmoidDerivLo, Real.sigmoidDeriv]
  exact le_trans (mulDown_le_mul _ _)
    (mul_le_mul h₁ h₂ h₀ (le_of_lt (Real.sigmoid_pos x)))

theorem le_sigmoidDerivHi (E : Enclosure 𝕋 Real.sigmoid) (l u : 𝕋) (x : ℝ)
    (hl : toReal l ≤ x) (hu : x ≤ toReal u) :
    Real.sigmoidDeriv x ≤ toReal (sigmoidDerivHi E l u) := by
  -- upward the sign needs no floor: an upper bound on a positive value is positive
  have h₁ : Real.sigmoid x ≤ toReal (E.hi u) := le_trans (Real.sigmoid_mono hu) (E.le_hi u)
  have h₂ : Real.sigmoid (-x) ≤ toReal (E.hi (neg l)) := by
    refine le_trans ?_ (E.le_hi (neg l))
    rw [toReal_neg]
    exact Real.sigmoid_mono (neg_le_neg hl)
  rw [sigmoidDerivHi, Real.sigmoidDeriv]
  exact le_trans (mul_le_mul h₁ h₂ (le_of_lt (Real.sigmoid_pos _))
    (le_trans (le_of_lt (Real.sigmoid_pos x)) h₁)) (mul_le_mulUp _ _)

/-! ## The relaxation

The secant is a guess and nothing more: `subDown u l` may be zero, where `divUp`
bounds nothing, and the clamp into the bracket is what makes that harmless. -/

def sigmoidSlope (E : Enclosure 𝕋 Real.sigmoid) (l u : 𝕋) : 𝕋 :=
  maximum (sigmoidDerivLo E l u)
    (minimum (sigmoidDerivHi E l u) (divUp (subUp (E.hi u) (E.lo l)) (subDown u l)))

noncomputable def sigmoidCurvatureRelaxation (E : Enclosure 𝕋 Real.sigmoid) :
    Relaxation 𝕋 Real.sigmoid :=
  Relaxation.ofDeriv Real.sigmoidDeriv Real.hasDerivAt_sigmoid E
    (sigmoidDerivLo E) (sigmoidDerivHi E) (sigmoidSlope E)
    (sigmoidDerivLo_le E) (le_sigmoidDerivHi E) fun l u h => by
      refine ⟨by rw [sigmoidSlope, toReal_maximum]; exact le_max_left _ _, ?_⟩
      rw [sigmoidSlope, toReal_maximum, toReal_minimum]
      exact max_le (le_trans (sigmoidDerivLo_le E l u (toReal l) le_rfl h)
        (le_sigmoidDerivHi E l u (toReal l) le_rfl h)) (min_le_left _ _)

/-- The curvature relaxation where its bracket pays for itself, and the
monotone one where it does not. `Layers/Tanh.lean` transports this whole. -/
noncomputable def sigmoidRelaxation (k : ℕ) : Relaxation 𝕋 Real.sigmoid :=
  (sigmoidCurvatureRelaxation (sigmoidEnclosure k)).tighter
    (Relaxation.ofMonotone Real.sigmoid_mono (sigmoidEnclosure k))

namespace Layer

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [IntervalOuter S 𝕋] [OfInterval S 𝕋] {n : ℕ}

/-- `k` is the exponential's reduction depth: every `k` is sound, a larger one
tighter, and it reaches both the value and the derivative bracket. -/
noncomputable def sigmoid (k : ℕ) : Real.Layer S n n := Layer.activation (sigmoidRelaxation k)

end Layer

end CORALean.Float
