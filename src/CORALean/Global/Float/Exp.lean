import CORALean.Global.Float.SoundFloatArithmetic

/-!
# A directed-rounding exponential

`expDown` and `expUp` enclose `Real.exp` at a float. They use `FloatOps` and
nothing else — no division, no factorials, no series.

## Why there is no series

A truncated exponential series divides by `k!`, and the three obvious ways to
pay for that — add division, supply reciprocal factorials as certified data, or
bound `1/k! ≤ 2^(1-k)` and accept the loss — all answer a question argument
reduction removes. `exp x = (exp (x / 2ⁿ))^(2ⁿ)`, and `half` is exact, so the
reduction is free; at `y = x / 2ⁿ` a *two-term* enclosure is already good to
`O(x²/2ⁿ)` relative, and the squarings carry it back. A geometric term bound
would do as well here — its 10% error at `x = 1` is a symptom of evaluating a
series at a large argument, not of the bound — so none of the three buys
anything, and the interface keeps the shape it had.

Division is added to `FloatOps` all the same, but for the layers above:
`sigmoid` and `tanh` are quotients, and neither has an `Enclosure` without one.
The exponential is not why it is there.

## The two seeds

Both are `Real.add_one_le_exp`, once at `y` and once at `-y`:

* `1 + y ≤ exp y`, at every real `y`;
* `exp y ≤ 1 / (1 - y)` for `y < 1`, and `1 / (1 - y) ≤ 1 + y + 2y²` exactly
  when `y ≤ 1/2`, since `(1 - y) * (1 + y + 2y²) = 1 + y² * (1 - 2y)`.

That is the whole remainder argument, and there is no tail in it because there
is no series to truncate. `n` squarings then lift a bound at `y` to one at
`2ⁿ y`, one rounding each.

## The asymmetry, which is real

`expDown` holds at every argument: its seed does, `maximum zero` keeps it
non-negative across the squarings, and squaring is monotone there.

`expUp n a` asks `toReal a ≤ 2ⁿ / 2`, and that hypothesis cannot be discharged
inside this class. Every expression `FloatOps` builds is a composition of `+`,
`*`, `min`, `max` and a halving, hence bounded by a polynomial, and no
polynomial dominates `exp` on all of ℝ. A total upper bound would have to branch
on the size of its argument, and `le` is deliberately unconstrained, so there is
nothing sound to branch on. The hypothesis is where that missing comparison
surfaces — which is why the sigmoid and tanh enclosures are written to ask for
`expDown` alone.

## What it costs

`(1 + x/2ⁿ)^(2ⁿ)` is `exp (x - x²/2ⁿ⁺¹ + …)`, so the lower bound's relative
error is about `x²/2ⁿ⁺¹` and the upper bound's about `3x²/2ⁿ⁺¹`, on top of `n`
roundings. At `n = 50` and `|x| ≤ 32` that is below `10⁻¹²` either way.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]

/-- `a / 2 ^ n`, exactly. -/
private def halfIter : ℕ → 𝕋 → 𝕋
  | 0, a => a
  | k + 1, a => half (halfIter k a)

/-- `1 + a`, floored at zero so the squarings stay monotone. -/
private def seedDown (a : 𝕋) : 𝕋 := maximum zero (addDown one a)

/-- `1 + a + 2a²`. The doubling is an addition rather than a product, so it
holds whatever the sign of `a`. -/
private def seedUp (a : 𝕋) : 𝕋 := addUp (addUp one a) (addUp (mulUp a a) (mulUp a a))

/-- `u ^ (2 ^ n)`, squaring `n` times rather than multiplying out. -/
private def squareDownIter : ℕ → 𝕋 → 𝕋
  | 0, u => u
  | k + 1, u => squareDownIter k (maximum zero (mulDown u u))

private def squareUpIter : ℕ → 𝕋 → 𝕋
  | 0, u => u
  | k + 1, u => squareUpIter k (mulUp u u)

/-- `exp a` from below, at every `a`. `n` is precision: the reduction is exact,
so a larger `n` only buys accuracy. -/
def expDown (n : ℕ) (a : 𝕋) : 𝕋 := squareDownIter n (seedDown (halfIter n a))

/-- `exp a` from above, for `toReal a ≤ 2 ^ n / 2`; see the module docstring for
why that hypothesis does not go away. -/
def expUp (n : ℕ) (a : 𝕋) : 𝕋 := squareUpIter n (seedUp (halfIter n a))

open SoundFloatArithmetic

variable [SoundFloatArithmetic 𝕋]

/-- `exp y ≤ 1/(1-y)` is `add_one_le_exp` at `-y`; `(1-y)(1+y+2y²) = 1+y²(1-2y)`
is where `y ≤ 1/2` is spent. -/
private theorem exp_le_quadratic {y : ℝ} (hy : y ≤ 1 / 2) :
    Real.exp y ≤ 1 + y + 2 * y ^ 2 := by
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

private theorem toReal_halfIter (n : ℕ) (a : 𝕋) :
    toReal (halfIter n a) = toReal a / 2 ^ n := by
  induction n with
  | zero => rw [halfIter, pow_zero, div_one]
  | succ k ih =>
    rw [halfIter, toReal_half, ih, pow_succ]
    ring

private theorem seedDown_nonneg (a : 𝕋) : 0 ≤ toReal (seedDown a) := by
  rw [seedDown, toReal_maximum, toReal_zero]
  exact le_max_left _ _

private theorem seedDown_le (a : 𝕋) : toReal (seedDown a) ≤ Real.exp (toReal a) := by
  rw [seedDown, toReal_maximum, toReal_zero]
  refine max_le (Real.exp_pos _).le (le_trans (addDown_le_add one a) ?_)
  rw [toReal_one]
  linarith [Real.add_one_le_exp (toReal a)]

private theorem le_seedUp {a : 𝕋} (ha : toReal a ≤ 1 / 2) :
    Real.exp (toReal a) ≤ toReal (seedUp a) := by
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

private theorem squareDownIter_nonneg (n : ℕ) {u : 𝕋} (hu : 0 ≤ toReal u) :
    0 ≤ toReal (squareDownIter n u) := by
  induction n generalizing u with
  | zero => rw [squareDownIter]; exact hu
  | succ k ih =>
    rw [squareDownIter]
    refine ih ?_
    rw [toReal_maximum, toReal_zero]
    exact le_max_left _ _

private theorem squareDownIter_le (n : ℕ) {u : 𝕋} {s : ℝ} (hu : 0 ≤ toReal u)
    (h : toReal u ≤ Real.exp s) : toReal (squareDownIter n u) ≤ Real.exp (2 ^ n * s) := by
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

private theorem le_squareUpIter (n : ℕ) {u : 𝕋} {s : ℝ} (h : Real.exp s ≤ toReal u) :
    Real.exp (2 ^ n * s) ≤ toReal (squareUpIter n u) := by
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

theorem expDown_le (n : ℕ) (a : 𝕋) : toReal (expDown n a) ≤ Real.exp (toReal a) := by
  have hpow : ((2:ℝ) ^ n) ≠ 0 := pow_ne_zero _ two_ne_zero
  have hle := seedDown_le (halfIter n a)
  rw [toReal_halfIter] at hle
  have hstep := squareDownIter_le n (seedDown_nonneg (halfIter n a)) hle
  rw [show (2:ℝ) ^ n * (toReal a / 2 ^ n) = toReal a by field_simp] at hstep
  rw [expDown]
  exact hstep

theorem le_expUp (n : ℕ) (a : 𝕋) (ha : toReal a ≤ 2 ^ n / 2) :
    Real.exp (toReal a) ≤ toReal (expUp n a) := by
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

end CORALean.Float
