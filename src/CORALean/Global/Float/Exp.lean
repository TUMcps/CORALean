module

public import CORALean.Global.Float.SoundFloatArithmetic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# A directed-rounding exponential

`expDown` and `expUp` enclose `Real.exp` at a float, out of `FloatOps` and
nothing else — no division, no factorials, no series. Argument reduction removes
the need for one: `exp x = (exp (x / 2ⁿ))^(2ⁿ)`, `half` is exact, and at
`y = x / 2ⁿ` a two-term enclosure is good to `O(x²/2ⁿ)` relative. Division is in
`FloatOps` for `sigmoid` and `tanh`, not for this. Both seeds are
`Real.add_one_le_exp`, once at `y` and once at `-y`: `1 + y ≤ exp y` everywhere,
and `exp y ≤ 1/(1-y) ≤ 1 + y + 2y²` for `y ≤ 1/2`.

The asymmetry is real. `expDown` holds at every argument, `maximum zero` keeping
it non-negative across the squarings; `expUp n a` keeps its hypothesis
`toReal a ≤ 2ⁿ / 2`. A sound `le` (issue #46) does not remove that: it lets a
caller *branch* on range, but the out-of-range branch still needs a sound value
to return, and no float bounds `exp` above at every argument — that needs
overflow handling (issue #48), not a comparison. What `le` buys is
`le_expUp_of_le`: discharging the hypothesis against a bound known in advance.
`(1 + x/2ⁿ)^(2ⁿ)` is `exp (x - x²/2ⁿ⁺¹ + …)`, under `10⁻¹²` relative at `n = 50`.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   04-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]

/-- `a / 2 ^ n`, exactly. -/
def halfIter : ℕ → 𝕋 → 𝕋
  | 0, a => a
  | k + 1, a => half (halfIter k a)

/-- `1 + a`, floored at zero so the squarings stay monotone. -/
def seedDown (a : 𝕋) : 𝕋 := maximum zero (addDown one a)

/-- `1 + a + 2a²`. The doubling is an addition rather than a product, so it
holds whatever the sign of `a`. -/
def seedUp (a : 𝕋) : 𝕋 := addUp (addUp one a) (addUp (mulUp a a) (mulUp a a))

/-- `u ^ (2 ^ n)`, squaring `n` times rather than multiplying out. -/
def squareDownIter : ℕ → 𝕋 → 𝕋
  | 0, u => u
  | k + 1, u => squareDownIter k (maximum zero (mulDown u u))

def squareUpIter : ℕ → 𝕋 → 𝕋
  | 0, u => u
  | k + 1, u => squareUpIter k (mulUp u u)

/-- `exp a` from below, at every `a`. `n` is the reduction depth: the halvings are exact, but each
of the `n` squarings rounds, so `n` should stay below the scalar's mantissa width (issue #131). -/
def expDown (n : ℕ) (a : 𝕋) : 𝕋 := squareDownIter n (seedDown (halfIter n a))

/-- `exp a` from above, for `toReal a ≤ 2 ^ n / 2`; see the module docstring for why that stays.
Sound but useless for `n` above the mantissa width, and can overflow the runtime (issue #131). -/
def expUp (n : ℕ) (a : 𝕋) : 𝕋 := squareUpIter n (seedUp (halfIter n a))

open SoundFloatArithmetic

variable [SoundFloatArithmetic 𝕋]

/-- `exp y ≤ 1/(1-y)` is `add_one_le_exp` at `-y`; `(1-y)(1+y+2y²) = 1+y²(1-2y)`
is where `y ≤ 1/2` is spent. -/
private theorem exp_le_quadratic {y : ℝ} (hy : y ≤ 1 / 2) :
    Real.exp y ≤ 1 + y + 2 * y ^ 2 := by -- --- PROOF ---
  have hpos : 0 < Real.exp y := Real.exp_pos y
  have h : 1 - y ≤ (Real.exp y)⁻¹ := by
    have hn := Real.add_one_le_exp (-y)
    rw [Real.exp_neg] at hn
    linarith
  have hmul : (1 - y) * Real.exp y ≤ 1 := by
    have h2 := mul_le_mul_of_nonneg_right h hpos.le
    rwa [inv_mul_cancel₀ (ne_of_gt hpos)] at h2
  have hq : (1 - y) * (1 + y + 2 * y ^ 2) - 1 = y ^ 2 * (1 - 2 * y) := by ring
  have hq0 : 0 ≤ y ^ 2 * (1 - 2 * y) := mul_nonneg (sq_nonneg y) (by linarith)
  exact le_of_mul_le_mul_left (by linarith) (by linarith : (0:ℝ) < 1 - y)

/-- `n` halvings divide by `2 ^ n` exactly, `half` rounding nothing. -/
private theorem toReal_halfIter (n : ℕ) (a : 𝕋) :
    toReal (halfIter n a) = toReal a / 2 ^ n := by -- --- PROOF ---
  induction n with
  | zero => rw [halfIter, pow_zero, div_one]
  | succ k ih =>
    rw [halfIter, toReal_half, ih, pow_succ]
    ring

/-- The `maximum zero` in the seed is what keeps the squarings monotone. -/
private theorem seedDown_nonneg (a : 𝕋) : 0 ≤ toReal (seedDown a) := by
  rw [seedDown, toReal_maximum, toReal_zero]
  exact le_max_left _ _

/-- The lower seed, `add_one_le_exp` at `a` after the rounding is paid. -/
private theorem seedDown_le (a : 𝕋) : toReal (seedDown a) ≤ Real.exp (toReal a) := by
  rw [seedDown, toReal_maximum, toReal_zero]
  refine max_le (Real.exp_pos _).le (le_trans (addDown_le_add one a) ?_)
  rw [toReal_one]
  linarith [Real.add_one_le_exp (toReal a)]

/-- The upper seed, `1 + y + 2y²` with each of its three roundings upward. -/
private theorem le_seedUp {a : 𝕋} (ha : toReal a ≤ 1 / 2) :
    Real.exp (toReal a) ≤ toReal (seedUp a) := by -- --- PROOF ---
  have h1 : toReal one + toReal a ≤ toReal (addUp one a) := add_le_addUp one a
  have h2 : toReal a * toReal a ≤ toReal (mulUp a a) := mul_le_mulUp a a
  have h3 : toReal (mulUp a a) + toReal (mulUp a a)
      ≤ toReal (addUp (mulUp a a) (mulUp a a)) := add_le_addUp _ _
  have h4 : toReal (addUp one a) + toReal (addUp (mulUp a a) (mulUp a a))
      ≤ toReal (seedUp a) := by
    rw [seedUp]
    exact add_le_addUp _ _
  have hsq : toReal a ^ 2 = toReal a * toReal a := sq (toReal a)
  rw [toReal_one] at h1
  linarith [exp_le_quadratic ha]

/-- Non-negativity survives the squarings, each clamped at zero. -/
private theorem squareDownIter_nonneg (n : ℕ) {u : 𝕋} (hu : 0 ≤ toReal u) :
    0 ≤ toReal (squareDownIter n u) := by -- --- PROOF ---
  induction n generalizing u with
  | zero => rw [squareDownIter]; exact hu
  | succ k ih =>
    rw [squareDownIter]
    refine ih ?_
    rw [toReal_maximum, toReal_zero]
    exact le_max_left _ _

/-- `n` downward squarings lift a bound at `s` to one at `2ⁿ s`. -/
private theorem squareDownIter_le (n : ℕ) {u : 𝕋} {s : ℝ} (hu : 0 ≤ toReal u)
    (h : toReal u ≤ Real.exp s) :
    toReal (squareDownIter n u) ≤ Real.exp (2 ^ n * s) := by -- --- PROOF ---
  induction n generalizing u s with
  | zero =>
    rw [squareDownIter, pow_zero, one_mul]
    exact h
  | succ k ih =>
    have hnn : 0 ≤ toReal (maximum zero (mulDown u u)) := by
      rw [toReal_maximum, toReal_zero]
      exact le_max_left _ _
    have hb : toReal (maximum zero (mulDown u u)) ≤ Real.exp (2 * s) := by
      rw [toReal_maximum, toReal_zero, show (2:ℝ) * s = s + s by ring, Real.exp_add]
      refine max_le (by positivity) (le_trans (mulDown_le_mul u u) ?_)
      exact mul_le_mul h h hu (Real.exp_pos s).le
    have hstep := ih hnn hb
    rw [show (2:ℝ) ^ k * (2 * s) = 2 ^ (k + 1) * s by rw [pow_succ]; ring] at hstep
    rw [squareDownIter]
    exact hstep

/-- The same upward, where no clamp is needed, an exponential being positive. -/
private theorem le_squareUpIter (n : ℕ) {u : 𝕋} {s : ℝ} (h : Real.exp s ≤ toReal u) :
    Real.exp (2 ^ n * s) ≤ toReal (squareUpIter n u) := by -- --- PROOF ---
  induction n generalizing u s with
  | zero =>
    rw [squareUpIter, pow_zero, one_mul]
    exact h
  | succ k ih =>
    have hb : Real.exp (2 * s) ≤ toReal (mulUp u u) := by
      have hnn : (0:ℝ) ≤ Real.exp s := (Real.exp_pos s).le
      have h2 : Real.exp s * Real.exp s ≤ toReal u * toReal u :=
        mul_le_mul h h hnn (le_trans hnn h)
      rw [show (2:ℝ) * s = s + s by ring, Real.exp_add]
      exact le_trans h2 (mul_le_mulUp u u)
    have hstep := ih hb
    rw [show (2:ℝ) ^ k * (2 * s) = 2 ^ (k + 1) * s by rw [pow_succ]; ring] at hstep
    rw [squareUpIter]
    exact hstep

/-- What makes the reciprocals above it total: a lower bound on an exponential
is never negative, so `1 + expDown a` is never below one. -/
theorem expDown_nonneg (n : ℕ) (a : 𝕋) : 0 ≤ toReal (expDown n a) :=
  squareDownIter_nonneg n (seedDown_nonneg _)

/-- The lower enclosure: seed at `a / 2ⁿ`, then square back. -/
theorem expDown_le (n : ℕ) (a : 𝕋) :
    toReal (expDown n a) ≤ Real.exp (toReal a) := by -- --- PROOF ---
  have hpow : ((2:ℝ) ^ n) ≠ 0 := pow_ne_zero _ two_ne_zero
  have hle := seedDown_le (halfIter n a)
  rw [toReal_halfIter] at hle
  have hstep := squareDownIter_le n (seedDown_nonneg (halfIter n a)) hle
  rw [show (2:ℝ) ^ n * (toReal a / 2 ^ n) = toReal a by field_simp] at hstep
  rw [expDown]
  exact hstep

/-- The upper enclosure, whose hypothesis is what puts `a / 2ⁿ` under `1/2`. -/
theorem le_expUp (n : ℕ) (a : 𝕋) (ha : toReal a ≤ 2 ^ n / 2) :
    Real.exp (toReal a) ≤ toReal (expUp n a) := by -- --- PROOF ---
  have hpow : (0:ℝ) < 2 ^ n := by positivity
  have hy : toReal (halfIter n a) ≤ 1 / 2 := by
    rw [toReal_halfIter, div_le_iff₀ hpow]
    linarith
  have hle := le_seedUp hy
  rw [toReal_halfIter] at hle
  have hstep := le_squareUpIter n hle
  rw [show (2:ℝ) ^ n * (toReal a / 2 ^ n) = toReal a by field_simp] at hstep
  rw [expUp]
  exact hstep


-- =======================================  MAIN THEOREM  ======================================= --

/-- The comparison earning its place: a caller holding a float `b` known to sit
at or below `2ⁿ / 2` discharges `le_expUp`'s hypothesis by comparing `a` against
it, rather than arguing about `toReal a` directly. -/
theorem le_expUp_of_le (n : ℕ) (a b : 𝕋) (hb : toReal b ≤ 2 ^ n / 2)
    (h : le a b = true) : Real.exp (toReal a) ≤ toReal (expUp n a) :=
  le_expUp n a (le_trans (toReal_le_of_le h) hb)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
