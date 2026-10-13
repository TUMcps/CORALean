module

public import CORALean.Global.Float.Log
public import CORALean.Global.Float.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Analysis.SpecialFunctions.Arcosh

@[expose] public section

/-!
# `arsinh` and `arcosh` rounded in either direction

Both are a logarithm of a root, `arsinh x = log (x + √(1 + x²))` and
`arcosh x = log (x + √(x² - 1))`, so both are `logUp`/`logDown` over `sqrtUp`/`sqrtDown`.
`k` is both the number of bisection steps of the logarithm and of Newton steps of the root, `p`
is `logDown`'s range exponent.

Upward, `x + √(1 + x²)` is positive at every `x`, so `asinhUp` needs no side condition, and
`acoshUp` only `1 ≤ x`. Downward, `logDown` wants an argument in `[1, 2ᵖ/2]`: the argument is
floored at `1`, which the true one exceeds, and the range is a hypothesis on `x`. Below zero
`arsinh` is odd, so the lower bound there is the upper one at `-x`, negated.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋]


/-- `arsinh x` from above, at every `x`. -/
def asinhUp (p k : ℕ) (x : 𝕋) : 𝕋 :=
  let radicand := addUp one (mulUp x x)
  logUp p k (addUp x (sqrtUp k radicand))

/-- `arsinh x` from below: the logarithm from below for `0 ≤ x`, the odd reflection otherwise. -/
def asinhDown (p k : ℕ) (x : 𝕋) : 𝕋 :=
  if le zero x = true then
    let radicand := addDown one (mulDown x x)
    logDown p k (maximum one (addDown x (sqrtDown k radicand)))
  else neg (asinhUp p k (neg x))

/-- `arcosh x` from above, for `1 ≤ x`. -/
def acoshUp (p k : ℕ) (x : 𝕋) : 𝕋 :=
  let radicand := subUp (mulUp x x) one
  logUp p k (addUp x (sqrtUp k radicand))

/-- `arcosh x` from below, for `1 ≤ x`. -/
def acoshDown (p k : ℕ) (x : 𝕋) : 𝕋 :=
  let radicand := subDown (mulDown x x) one
  logDown p k (maximum one (addDown x (sqrtDown k radicand)))

variable [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

private theorem sqrt_pos_arg {x : ℝ} : 0 < x + Real.sqrt (1 + x ^ 2) := by
  rw [← neg_lt_iff_pos_add']
  exact Real.lt_sqrt_of_sq_lt (by simp)

theorem le_asinhUp (p k : ℕ) (x : 𝕋) :
    Real.arsinh (toReal x) ≤ toReal (asinhUp p k x) := by -- --- PROOF ---
  have hs := le_sqrtUp k (addUp one (mulUp x x))
  have hr : 1 + toReal x ^ 2 ≤ toReal (addUp one (mulUp x x)) := by
    have h1 := add_le_addUp (one : 𝕋) (mulUp x x)
    have h2 := mul_le_mulUp x x
    rw [toReal_one] at h1
    nlinarith
  have hT : 0 < toReal x + Real.sqrt (1 + toReal x ^ 2) := sqrt_pos_arg
  have hC : toReal x + Real.sqrt (1 + toReal x ^ 2) ≤
      toReal (addUp x (sqrtUp k (addUp one (mulUp x x)))) := by
    have := add_le_addUp x (sqrtUp k (addUp one (mulUp x x)))
    have := Real.sqrt_le_sqrt hr
    linarith
  refine le_trans (Real.log_le_log hT hC) ?_
  exact le_logUp p k _ (lt_of_lt_of_le hT hC)

theorem asinhDown_le (p k : ℕ) (x : 𝕋)
    (hx : 0 ≤ toReal x → 2 * toReal x + 1 ≤ 2 ^ p / 2) :
    toReal (asinhDown p k x) ≤ Real.arsinh (toReal x) := by -- --- PROOF ---
  unfold asinhDown
  split_ifs with h
  · have h0 : 0 ≤ toReal x := by
      have := toReal_le_of_le h
      rwa [toReal_zero] at this
    have hr : toReal (addDown one (mulDown x x)) ≤ 1 + toReal x ^ 2 := by
      have h1 := addDown_le_add (one : 𝕋) (mulDown x x)
      have h2 := mulDown_le_mul x x
      rw [toReal_one] at h1
      nlinarith
    have hs := le_trans (sqrtDown_le k (addDown one (mulDown x x))) (Real.sqrt_le_sqrt hr)
    -- the true argument is at least `1` and at most `2x + 1`
    have hT1 : 1 ≤ toReal x + Real.sqrt (1 + toReal x ^ 2) := by
      have : 1 ≤ Real.sqrt (1 + toReal x ^ 2) := by
        rw [Real.le_sqrt (by norm_num) (by positivity)]; nlinarith
      linarith
    have hTle : toReal x + Real.sqrt (1 + toReal x ^ 2) ≤ 2 * toReal x + 1 := by
      have : Real.sqrt (1 + toReal x ^ 2) ≤ toReal x + 1 := by
        rw [Real.sqrt_le_left (by linarith)]; nlinarith
      linarith
    -- the floored computed argument sits between `1` and the true one
    have hL := addDown_le_add x (sqrtDown k (addDown one (mulDown x x)))
    have hB : toReal (maximum one (addDown x (sqrtDown k (addDown one (mulDown x x))))) ≤
        toReal x + Real.sqrt (1 + toReal x ^ 2) := by
      rw [toReal_maximum, toReal_one]
      exact max_le hT1 (by linarith)
    have hB1 : 1 ≤ toReal (maximum one (addDown x (sqrtDown k (addDown one (mulDown x x))))) := by
      rw [toReal_maximum, toReal_one]; exact le_max_left _ _
    refine le_trans (logDown_le p k _ hB1 (le_trans hB (le_trans hTle (hx h0)))) ?_
    exact Real.log_le_log (lt_of_lt_of_le one_pos hB1) hB
  · have := le_asinhUp p k (neg x)
    rw [toReal_neg] at this ⊢
    rw [Real.arsinh_neg] at this
    linarith [this]

theorem le_acoshUp (p k : ℕ) (x : 𝕋) (hx : 1 ≤ toReal x) :
    Real.arcosh (toReal x) ≤ toReal (acoshUp p k x) := by -- --- PROOF ---
  have hs := le_sqrtUp k (subUp (mulUp x x) one)
  have hr : toReal x ^ 2 - 1 ≤ toReal (subUp (mulUp x x) one) := by
    have h1 := sub_le_subUp (mulUp x x) (one : 𝕋)
    have h2 := mul_le_mulUp x x
    rw [toReal_one] at h1
    nlinarith
  have hT : 0 < toReal x + Real.sqrt (toReal x ^ 2 - 1) := by positivity
  have hC : toReal x + Real.sqrt (toReal x ^ 2 - 1) ≤
      toReal (addUp x (sqrtUp k (subUp (mulUp x x) one))) := by
    have := add_le_addUp x (sqrtUp k (subUp (mulUp x x) one))
    have := Real.sqrt_le_sqrt hr
    linarith
  refine le_trans (Real.log_le_log hT hC) ?_
  exact le_logUp p k _ (lt_of_lt_of_le hT hC)

theorem acoshDown_le (p k : ℕ) (x : 𝕋) (h1 : 1 ≤ toReal x) (hx : 2 * toReal x ≤ 2 ^ p / 2) :
    toReal (acoshDown p k x) ≤ Real.arcosh (toReal x) := by -- --- PROOF ---
  have hr : toReal (subDown (mulDown x x) one) ≤ toReal x ^ 2 - 1 := by
    have h1 := subDown_le_sub (mulDown x x) (one : 𝕋)
    have h2 := mulDown_le_mul x x
    rw [toReal_one] at h1
    nlinarith
  have hs := le_trans (sqrtDown_le k (subDown (mulDown x x) one)) (Real.sqrt_le_sqrt hr)
  -- the true argument is at least `1` and at most `2x`
  have hT1 : 1 ≤ toReal x + Real.sqrt (toReal x ^ 2 - 1) := by
    linarith [Real.sqrt_nonneg (toReal x ^ 2 - 1)]
  have hTle : toReal x + Real.sqrt (toReal x ^ 2 - 1) ≤ 2 * toReal x := by
    have : Real.sqrt (toReal x ^ 2 - 1) ≤ toReal x := by
      rw [Real.sqrt_le_left (by linarith)]; nlinarith
    linarith
  -- the floored computed argument sits between `1` and the true one
  have hL := addDown_le_add x (sqrtDown k (subDown (mulDown x x) one))
  have hB : toReal (maximum one (addDown x (sqrtDown k (subDown (mulDown x x) one)))) ≤
      toReal x + Real.sqrt (toReal x ^ 2 - 1) := by
    rw [toReal_maximum, toReal_one]
    exact max_le hT1 (by linarith)
  have hB1 : 1 ≤ toReal (maximum one (addDown x (sqrtDown k (subDown (mulDown x x) one)))) := by
    rw [toReal_maximum, toReal_one]; exact le_max_left _ _
  refine le_trans (logDown_le p k _ hB1 (le_trans hB (le_trans hTle hx))) ?_
  exact Real.log_le_log (lt_of_lt_of_le one_pos hB1) hB

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
