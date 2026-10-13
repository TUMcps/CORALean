module

public import CORALean.Global.Float.Exp
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

/-!
# A directed-rounding logarithm

`logDown` and `logUp` enclose `Real.log` at a float and compute no series:
`log` is inverted rather than evaluated. A candidate `s` bounds `log a` from
below exactly when `exp s ≤ a`, and `expUp` bounds `exp s` from above, so
`le (expUp n s) a` *certifies* `s` — `EuclideanNorm`'s pattern with `expUp` in
place of a squaring. Bisection over `[0, a]` turns the check into a value: each
step keeps the endpoint its own check certified, so the one returned is.

Hence the domain. `Real.log x = 0` for `x ≤ 0` is a junk value, and neither
theorem leans on it: `le_logUp` asks `0 < toReal a`, `logDown_le` asks
`1 ≤ toReal a`, which is what makes `zero` a certified left endpoint. Below one
a caller reflects, `log a = -log (1 / a)`.

`logDown` inherits `expUp`'s hypothesis `toReal a ≤ 2ⁿ / 2` — no candidate ever
exceeds `a` — and `logDown_le_of_le` discharges it by comparison. `logUp` goes
through `expDown`, which carries no hypothesis, so neither does it.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]

/-- The bisection midpoint, its one rounding downward so that a bracket under a
bound stays under it. -/
def mid (lo hi : 𝕋) : 𝕋 := half (addDown lo hi)

/-- Bisecting for a lower bound: the midpoint becomes the new `lo` where `expUp`
clears it against `a`, and caps the bracket where it does not. -/
def logDownIter (n : ℕ) (a : 𝕋) : ℕ → 𝕋 → 𝕋 → 𝕋
  | 0, lo, _ => lo
  | k + 1, lo, hi =>
    if le (expUp n (mid lo hi)) a = true then logDownIter n a k (mid lo hi) hi
    else logDownIter n a k lo (mid lo hi)

/-- The reflection: `expDown` clearing the midpoint from the other side is what
lets it replace `hi`. -/
def logUpIter (n : ℕ) (a : 𝕋) : ℕ → 𝕋 → 𝕋 → 𝕋
  | 0, _, hi => hi
  | k + 1, lo, hi =>
    if le a (expDown n (mid lo hi)) = true then logUpIter n a k lo (mid lo hi)
    else logUpIter n a k (mid lo hi) hi

/-- `log a` from below, for `1 ≤ a`. `n` is `expUp`'s precision and `k` the
number of bisection steps; the bracket `[0, a]` holds `log a`. -/
def logDown (n k : ℕ) (a : 𝕋) : 𝕋 := logDownIter n a k zero a

/-- `log a` from above, for `0 < a`, bisecting the same bracket. -/
def logUp (n k : ℕ) (a : 𝕋) : 𝕋 := logUpIter n a k zero a

open SoundFloatArithmetic

variable [SoundFloatArithmetic 𝕋]

/-- Rounded down, a midpoint of two floats under a bound is under it too. -/
private theorem mid_le {lo hi : 𝕋} {B : ℝ} (hlo : toReal lo ≤ B) (hhi : toReal hi ≤ B) :
    toReal (mid lo hi) ≤ B := by
  rw [mid, toReal_half]
  linarith [addDown_le_add lo hi]

/-- The invariant carried down: `lo` is certified, and both ends stay inside
`expUp`'s range, which is what lets the next midpoint be tested at all. -/
private theorem logDownIter_le (n : ℕ) (a : 𝕋) : ∀ (k : ℕ) (lo hi : 𝕋),
    Real.exp (toReal lo) ≤ toReal a → toReal lo ≤ 2 ^ n / 2 → toReal hi ≤ 2 ^ n / 2 →
    Real.exp (toReal (logDownIter n a k lo hi)) ≤ toReal a := by -- --- PROOF ---
  intro k
  induction k with
  | zero =>
    intro lo hi h _ _
    rw [logDownIter]
    exact h
  | succ k ih =>
    intro lo hi h hlo hhi
    have hm : toReal (mid lo hi) ≤ 2 ^ n / 2 := mid_le hlo hhi
    rw [logDownIter]
    by_cases hc : le (expUp n (mid lo hi)) a = true
    · rw [if_pos hc]
      exact ih _ _ (le_trans (le_expUp n _ hm) (toReal_le_of_le hc)) hm hhi
    · rw [if_neg hc]
      exact ih _ _ h hlo hm

/-- The invariant carried up is the shorter one: `expDown` needs no range, so
only the certificate on `hi` travels. -/
private theorem le_logUpIter (n : ℕ) (a : 𝕋) : ∀ (k : ℕ) (lo hi : 𝕋),
    toReal a ≤ Real.exp (toReal hi) →
    toReal a ≤ Real.exp (toReal (logUpIter n a k lo hi)) := by -- --- PROOF ---
  intro k
  induction k with
  | zero =>
    intro lo hi h
    rw [logUpIter]
    exact h
  | succ k ih =>
    intro lo hi h
    rw [logUpIter]
    by_cases hc : le a (expDown n (mid lo hi)) = true
    · rw [if_pos hc]
      exact ih _ _ (le_trans (toReal_le_of_le hc) (expDown_le n (mid lo hi)))
    · rw [if_neg hc]
      exact ih _ _ h

/-- The lower enclosure. `1 ≤ a` is what certifies the left endpoint `zero`, and
the range bound is `expUp`'s, which no candidate under `a` escapes. -/
theorem logDown_le (n k : ℕ) (a : 𝕋) (h1 : 1 ≤ toReal a) (hn : toReal a ≤ 2 ^ n / 2) :
    toReal (logDown n k a) ≤ Real.log (toReal a) := by -- --- PROOF ---
  have hpos : (0:ℝ) < toReal a := lt_of_lt_of_le zero_lt_one h1
  have hz : Real.exp (toReal (zero : 𝕋)) ≤ toReal a := by
    rw [toReal_zero, Real.exp_zero]
    exact h1
  have hzb : toReal (zero : 𝕋) ≤ 2 ^ n / 2 := by
    rw [toReal_zero]
    positivity
  rw [logDown, Real.le_log_iff_exp_le hpos]
  exact logDownIter_le n a k zero a hz hzb hn

/-- The upper enclosure, whose one hypothesis is what keeps `Real.log` off its
junk value; `a ≤ exp a` is what certifies the right endpoint. -/
theorem le_logUp (n k : ℕ) (a : 𝕋) (ha : 0 < toReal a) :
    Real.log (toReal a) ≤ toReal (logUp n k a) := by
  have hz : toReal a ≤ Real.exp (toReal a) := by
    linarith [Real.add_one_le_exp (toReal a)]
  rw [logUp, Real.log_le_iff_le_exp ha]
  exact le_logUpIter n a k zero a hz


-- =======================================  MAIN THEOREM  ======================================= --

/-- Both hypotheses of `logDown_le` discharged by comparison: `one ≤ a` for the
left endpoint, and `a ≤ b` for a `b` the caller already knows `expUp` covers. -/
theorem logDown_le_of_le (n k : ℕ) (a b : 𝕋) (hb : toReal b ≤ 2 ^ n / 2)
    (h1 : le one a = true) (h : le a b = true) :
    toReal (logDown n k a) ≤ Real.log (toReal a) := by
  refine logDown_le n k a ?_ (le_trans (toReal_le_of_le h) hb)
  have hone := toReal_le_of_le h1
  rwa [toReal_one] at hone

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
