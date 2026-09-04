import CORALean.NN.Float.Layers.Activation
import CORALean.NN.Layers.ReLU

/-!
# The ReLU layer over a floating-point scalar

The one standard activation that needs no transcendental function, and the one
carrying a nonzero slope. Over ℝ that slope is the secant `u / (u - l)`.

Which direction that division rounds is of no consequence. The slope is a
precision knob and never a correctness condition: any value in `[0, 1]` is sound,
and the error is measured against the value stored. So `clampUnit` brings an
unverified guess into range with `minimum` and `maximum`, both exact.

What has to round is the gap, and it rounds up: `(1 - λ) u` from the directed
difference and `-λ l` from the negated rounded-down product, the larger of the
two. Halving is exact, so the recentred relaxation is `± gap / 2`.

`reluSlope` is the default: exact on a stable neuron and the secant on a crossing
one, rounded whichever way `divUp` rounds. It reads `le`, which
`SoundFloatArithmetic` constrains in no way, and does not have to.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

-- not `Matrix`: its `zero` would make `FloatOps.zero` ambiguous
open ContSet FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]

/-- Any candidate becomes a legal slope. `minimum` and `maximum` are exact, so
this needs no rounding axiom and no decidable order on what the floats denote. -/
def clampUnit (c : 𝕋) : 𝕋 := maximum zero (minimum one c)

theorem clampUnit_nonneg (c : 𝕋) : 0 ≤ toReal (clampUnit c) := by
  rw [clampUnit, toReal_maximum, toReal_zero]
  exact le_max_left _ _

theorem clampUnit_le_one (c : 𝕋) : toReal (clampUnit c) ≤ 1 := by
  rw [clampUnit, toReal_maximum, toReal_minimum, toReal_zero, toReal_one]
  exact max_le zero_le_one (min_le_left _ _)

/-- The gap that slope leaves, rounded up on both ends. -/
def reluGapUp (lam l u : 𝕋) : 𝕋 :=
  maximum (subUp u (mulDown lam u)) (neg (mulDown lam l))

theorem reluGapOfSlope_le (lam l u : 𝕋) :
    Real.reluGapOfSlope (toReal lam) (toReal l) (toReal u) ≤ toReal (reluGapUp lam l u) := by
  have hexp : (1 - toReal lam) * toReal u = toReal u - toReal lam * toReal u := by ring
  have h1 : (1 - toReal lam) * toReal u ≤ toReal (subUp u (mulDown lam u)) := by
    have ha := sub_le_subUp u (mulDown lam u)
    have hb := mulDown_le_mul lam u
    rw [hexp]
    linarith
  have h2 : -(toReal lam * toReal l) ≤ toReal (neg (mulDown lam l)) := by
    have hb := mulDown_le_mul lam l
    rw [toReal_neg]
    linarith
  rw [Real.reluGapOfSlope, reluGapUp, toReal_maximum]
  exact max_le (le_trans h1 (le_max_left _ _)) (le_trans h2 (le_max_right _ _))

/-- Recentred, so that the error is half the gap in each direction, exactly as
over ℝ — halving a float moves only the exponent. -/
def reluRelaxation (lam : 𝕋 → 𝕋 → 𝕋) : Relaxation 𝕋 Real.relu where
  slope l u := clampUnit (lam l u)
  offset l u := half (reluGapUp (clampUnit (lam l u)) l u)
  error l u := half (reluGapUp (clampUnit (lam l u)) l u)
  sound {l u _t} hl hu := by
    obtain ⟨hlow, hhigh⟩ := Real.relu_bounds_of_slope (clampUnit_nonneg (lam l u))
      (clampUnit_le_one (lam l u)) hl hu
    have hg := reluGapOfSlope_le (clampUnit (lam l u)) l u
    rw [toReal_half, abs_le]
    exact ⟨by linarith, by linarith⟩

/-- Exact on a stable neuron; the secant where the neuron crosses. A caller with
a better candidate passes it to `Layer.relu` instead, and pays nothing for the
change. -/
def reluSlope (l u : 𝕋) : 𝕋 :=
  if le u zero then zero else if le zero l then one else divUp u (subDown u l)

namespace Layer

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [IntervalOuter S 𝕋] [OfInterval S 𝕋] {n : ℕ}

def relu (lam : 𝕋 → 𝕋 → 𝕋 := reluSlope) : Real.Layer S n n :=
  Layer.activation (reluRelaxation lam)

end Layer

end CORALean.Float
