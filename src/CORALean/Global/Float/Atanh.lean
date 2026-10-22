module

public import CORALean.Global.Float.Log
public import Mathlib.Analysis.SpecialFunctions.Artanh

@[expose] public section

/-!
# `artanh` rounded in either direction

`artanh x = ½ log ((1 + x)/(1 - x))` on `(-1, 1)`, so `atanhUp`/`atanhDown` are `half` of
`logUp`/`logDown` of a ratio rounded the same way; `p` is `logDown`'s range exponent and `k` the
number of bisection steps. Upward, the divisor `1 - x` is rounded down and has to be proved
positive, and the argument exceeds `-1`: both are hypotheses. `logDown` only accepts an argument of
at least `1`, which the ratio is for `0 ≤ x`, so there the lower bound is `logDown` of the ratio
floored at `1`; below zero `artanh` is odd and the lower bound is the upper one at `-x`, negated.
`le zero x` answers only `true` reliably, so the odd branch also covers an `x` of undecided sign.

## Inputs
* `x` – real argument

## Hypotheses
* `h1` – the argument exceeds minus one
* `h2` – the argument is below one

## Conclusion
* `artanh` is an odd function
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋]


/-- `artanh x` from above, for `-1 < x < 1`. -/
def atanhUp (p k : ℕ) (x : 𝕋) : 𝕋 :=
  let ratio := divUp (addUp one x) (subDown one x)
  half (logUp p k ratio)

/-- `artanh x` from below, for `-1 < x < 1`: `logDown` of the ratio for `0 ≤ x`, the odd
reflection otherwise. -/
def atanhDown (p k : ℕ) (x : 𝕋) : 𝕋 :=
  if le zero x = true then
    let ratio := divDown (addDown one x) (subUp one x)
    half (logDown p k (maximum one ratio))
  else neg (atanhUp p k (neg x))

variable [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

private theorem artanh_neg_eq {x : ℝ} (h1 : -1 < x) (h2 : x < 1) : -- --- CONCL ---
    Real.artanh (-x) = -Real.artanh x := by -- --- PROOF ---
  rw [Real.artanh_eq_half_log ⟨by linarith, by linarith⟩,
    Real.artanh_eq_half_log ⟨h1.le, h2.le⟩]
  have : (1 + -x) / (1 - -x) = ((1 + x) / (1 - x))⁻¹ := by
    rw [inv_div]; ring_nf
  rw [this, Real.log_inv]
  ring

/-- `atanhUp` is an upper bound of `artanh` for `x > -1` when `1 - x` rounded down is positive. -/
theorem le_atanhUp (p k : ℕ) (x : 𝕋) (h1 : -1 < toReal x)
    (h2 : 0 < toReal (subDown one x)) : -- --- CONCL ---
    Real.artanh (toReal x) ≤ toReal (atanhUp p k x) := by -- --- PROOF ---
  have hD := subDown_le_sub (one : 𝕋) x
  have hN := add_le_addUp (one : 𝕋) x
  rw [toReal_one] at hD hN
  have hx1 : toReal x < 1 := by linarith
  have hr : (1 + toReal x) / (1 - toReal x) ≤ toReal (divUp (addUp one x) (subDown one x)) := by
    refine le_trans ?_ (div_le_divUp _ _ h2)
    calc (1 + toReal x) / (1 - toReal x)
        ≤ (1 + toReal x) / toReal (subDown one x) :=
          div_le_div_of_nonneg_left (by linarith) h2 hD
      _ ≤ toReal (addUp one x) / toReal (subDown one x) :=
          div_le_div_of_nonneg_right (by linarith) h2.le
  have hpos : 0 < (1 + toReal x) / (1 - toReal x) := div_pos (by linarith) (by linarith)
  rw [Real.artanh_eq_half_log ⟨h1.le, hx1.le⟩, atanhUp, toReal_half]
  have := le_logUp p k (divUp (addUp one x) (subDown one x)) (lt_of_lt_of_le hpos hr)
  have := Real.log_le_log hpos hr
  linarith

/-- `atanhDown` is a lower bound of `artanh` for `x < 1`, with the ratio bound `2^p / 2` for `x ≥
0`. -/
theorem atanhDown_le (p k : ℕ) (x : 𝕋) (h1 : toReal x < 1)
    (h2 : 0 < toReal (subDown one (neg x)))
    (hx : 0 ≤ toReal x → (1 + toReal x) / (1 - toReal x) ≤ 2 ^ p / 2) : -- --- CONCL ---
    toReal (atanhDown p k x) ≤ Real.artanh (toReal x) := by -- --- PROOF ---
  unfold atanhDown
  split_ifs with h
  · have h0 : 0 ≤ toReal x := by
      have := toReal_le_of_le h
      rwa [toReal_zero] at this
    have hD := sub_le_subUp (one : 𝕋) x
    have hN := addDown_le_add (one : 𝕋) x
    rw [toReal_one] at hD hN
    have hDpos : 0 < toReal (subUp one x) := by linarith
    have hq := divDown_le_div (addDown one x) (subUp one x) hDpos
    -- the computed ratio is below the true one, which is at least `1`
    have hr1 : 1 ≤ (1 + toReal x) / (1 - toReal x) := by
      rw [le_div_iff₀ (by linarith)]; linarith
    have hq' : toReal (divDown (addDown one x) (subUp one x)) ≤
        (1 + toReal x) / (1 - toReal x) := by
      refine le_trans hq (le_trans (div_le_div_of_nonneg_right hN hDpos.le) ?_)
      exact div_le_div_of_nonneg_left (by linarith) (by linarith) hD
    have hB : toReal (maximum one (divDown (addDown one x) (subUp one x))) ≤
        (1 + toReal x) / (1 - toReal x) := by
      rw [toReal_maximum, toReal_one]; exact max_le hr1 hq'
    have hB1 : 1 ≤ toReal (maximum one (divDown (addDown one x) (subUp one x))) := by
      rw [toReal_maximum, toReal_one]; exact le_max_left _ _
    -- `logDown` applies: the floored argument is in `[1, 2ᵖ/2]`
    have hL := logDown_le p k _ hB1 (le_trans hB (hx h0))
    have hlog := Real.log_le_log (lt_of_lt_of_le one_pos hB1) hB
    rw [Real.artanh_eq_half_log ⟨by linarith, h1.le⟩, toReal_half]
    linarith
  · have hD := subDown_le_sub (one : 𝕋) (neg x)
    rw [toReal_one, toReal_neg] at hD
    have := le_atanhUp p k (neg x) (by rw [toReal_neg]; linarith) h2
    rw [toReal_neg, artanh_neg_eq (by linarith) (by linarith)] at this
    rw [toReal_neg]
    linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
