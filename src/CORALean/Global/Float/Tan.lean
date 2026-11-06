module

public import CORALean.Global.Float.SinCos
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

/-!
# The tangent rounded in either direction

`tan x = sin x / cos x`, the sine bound over the two bounds on the cosine. The quotient is only
bounded where the cosine is certified positive, so both carry the hypothesis
`0 < toReal (cosDown n x)`, which a caller discharges by evaluating `cosDown` (`ltStrict` against
`zero` certifies it), as `le_expUp_of_le` discharges `expUp`'s range. No fallback is possible:
the tangent is unbounded. Where the cosine is negative, `tan x = (-sin x) / (-cos x)` is the same
quotient by the positive `-cos x` (`tanDownNeg`, `tanUpNeg`, bounded where `cosUp` is negative).
`piBelow` is a float below `π`, which `Interval.tan` compares a range's width with.

## Inputs
* `n` – number of halvings
* `x` – float argument

## Hypotheses
* `hc` – the downward cosine bound is positive

## Conclusion
* the downward tangent bound is at most the tangent
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   03-November-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]

/-- `tan x` from below, where `cosDown n x` is positive. -/
def tanDown (n : ℕ) (x : 𝕋) : 𝕋 :=
  let cl := cosDown n x
  let cu := cosUp n x
  let sl := sinDown n x
  minimum (divDown sl cl) (divDown sl cu)

/-- `tan x` from above, where `cosDown n x` is positive. -/
def tanUp (n : ℕ) (x : 𝕋) : 𝕋 :=
  let cl := cosDown n x
  let cu := cosUp n x
  let su := sinUp n x
  maximum (divUp su cl) (divUp su cu)

/-- `tan x` from below, where `cosUp n x` is negative: `tan x = (-sin x) / (-cos x)`, the quotient
by the positive `-cos x`. -/
def tanDownNeg (n : ℕ) (x : 𝕋) : 𝕋 :=
  let cl := cosDown n x
  let cu := cosUp n x
  let su := sinUp n x
  minimum (divDown (neg su) (neg cu)) (divDown (neg su) (neg cl))

/-- `tan x` from above, where `cosUp n x` is negative. -/
def tanUpNeg (n : ℕ) (x : 𝕋) : 𝕋 :=
  let cl := cosDown n x
  let cu := cosUp n x
  let sl := sinDown n x
  maximum (divUp (neg sl) (neg cu)) (divUp (neg sl) (neg cl))

/-- A float below `π`: `3 + 1/8`, each sum rounded down. The widest range the pole test of
`Interval.tan` accepts. -/
def piBelow : 𝕋 := addDown (addDown one (addDown one one)) (half (half (half one)))

open SoundFloatArithmetic

variable [SoundFloatArithmetic 𝕋]

/-- `s / c` between `s` over the two bounds on a positive `c`. -/
private theorem div_between (s : ℝ) {c cl cu : ℝ} (hl : 0 < cl) (h1 : cl ≤ c)
    (h2 : c ≤ cu) : -- --- CONCL ---
    min (s / cl) (s / cu) ≤ s / c ∧ s / c ≤ max (s / cl) (s / cu) := by -- --- PROOF ---
  have hc : 0 < c := lt_of_lt_of_le hl h1
  have i1 : c⁻¹ ≤ cl⁻¹ := inv_anti₀ hl h1
  have i2 : cu⁻¹ ≤ c⁻¹ := inv_anti₀ hc h2
  simp only [div_eq_mul_inv]
  rcases le_total 0 s with hs | hs
  · exact ⟨min_le_of_right_le (mul_le_mul_of_nonneg_left i2 hs),
      le_max_of_le_left (mul_le_mul_of_nonneg_left i1 hs)⟩
  · exact ⟨min_le_of_left_le (mul_le_mul_of_nonpos_left i1 hs),
      le_max_of_le_right (mul_le_mul_of_nonpos_left i2 hs)⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem tanDown_le (n : ℕ) (x : 𝕋) (hc : 0 < toReal (cosDown n x)) : -- --- CONCL ---
    toReal (tanDown n x) ≤ Real.tan (toReal x) := by -- --- PROOF ---
  have h1 := cosDown_le n x
  have h2 := le_cosUp n x
  have hcu : 0 < toReal (cosUp n x) := by linarith
  have hcx : 0 < Real.cos (toReal x) := by linarith
  have hb := div_between (toReal (sinDown n x)) hc h1 h2
  rw [Real.tan_eq_sin_div_cos]
  refine le_trans ?_ (le_trans hb.1 (div_le_div_of_nonneg_right (sinDown_le n x) hcx.le))
  simp only [tanDown, toReal_minimum]
  exact min_le_min (divDown_le_div _ _ hc) (divDown_le_div _ _ hcu)

/-- `tanUp` is an upper bound of `tan` where `cosDown` is positive. -/
theorem le_tanUp (n : ℕ) (x : 𝕋) (hc : 0 < toReal (cosDown n x)) : -- --- CONCL ---
    Real.tan (toReal x) ≤ toReal (tanUp n x) := by -- --- PROOF ---
  have h1 := cosDown_le n x
  have h2 := le_cosUp n x
  have hcu : 0 < toReal (cosUp n x) := by linarith
  have hcx : 0 < Real.cos (toReal x) := by linarith
  have hb := div_between (toReal (sinUp n x)) hc h1 h2
  rw [Real.tan_eq_sin_div_cos]
  refine le_trans (le_trans (div_le_div_of_nonneg_right (le_sinUp n x) hcx.le) hb.2) ?_
  simp only [tanUp, toReal_maximum]
  exact max_le_max (div_le_divUp _ _ hc) (div_le_divUp _ _ hcu)

/-- `tanDownNeg` is a lower bound of `tan` where `cosUp` is negative. -/
theorem tanDownNeg_le (n : ℕ) (x : 𝕋) (hc : toReal (cosUp n x) < 0) : -- --- CONCL ---
    toReal (tanDownNeg n x) ≤ Real.tan (toReal x) := by -- --- PROOF ---
  have h1 := cosDown_le n x
  have h2 := le_cosUp n x
  have hcl : 0 < toReal (neg (cosUp n x)) := by rw [toReal_neg]; linarith
  have hcu : 0 < toReal (neg (cosDown n x)) := by rw [toReal_neg]; linarith
  have hcx : 0 < -Real.cos (toReal x) := by linarith
  have hb := div_between (c := -Real.cos (toReal x)) (cu := toReal (neg (cosDown n x)))
    (toReal (neg (sinUp n x))) hcl
    (by rw [toReal_neg]; linarith) (by rw [toReal_neg]; linarith)
  have hs : toReal (neg (sinUp n x)) ≤ -Real.sin (toReal x) := by
    rw [toReal_neg]; linarith [le_sinUp n x]
  have e : Real.tan (toReal x) = -Real.sin (toReal x) / -Real.cos (toReal x) := by
    rw [Real.tan_eq_sin_div_cos, neg_div_neg_eq]
  rw [e]
  refine le_trans ?_ (le_trans hb.1 (div_le_div_of_nonneg_right hs hcx.le))
  simp only [tanDownNeg, toReal_minimum]
  exact min_le_min (divDown_le_div _ _ hcl) (divDown_le_div _ _ hcu)

/-- `tanUpNeg` is an upper bound of `tan` where `cosUp` is negative. -/
theorem le_tanUpNeg (n : ℕ) (x : 𝕋) (hc : toReal (cosUp n x) < 0) : -- --- CONCL ---
    Real.tan (toReal x) ≤ toReal (tanUpNeg n x) := by -- --- PROOF ---
  have h1 := cosDown_le n x
  have h2 := le_cosUp n x
  have hcl : 0 < toReal (neg (cosUp n x)) := by rw [toReal_neg]; linarith
  have hcu : 0 < toReal (neg (cosDown n x)) := by rw [toReal_neg]; linarith
  have hcx : 0 < -Real.cos (toReal x) := by linarith
  have hb := div_between (c := -Real.cos (toReal x)) (cu := toReal (neg (cosDown n x)))
    (toReal (neg (sinDown n x))) hcl
    (by rw [toReal_neg]; linarith) (by rw [toReal_neg]; linarith)
  have hs : -Real.sin (toReal x) ≤ toReal (neg (sinDown n x)) := by
    rw [toReal_neg]; linarith [sinDown_le n x]
  have e : Real.tan (toReal x) = -Real.sin (toReal x) / -Real.cos (toReal x) := by
    rw [Real.tan_eq_sin_div_cos, neg_div_neg_eq]
  rw [e]
  refine le_trans (le_trans (div_le_div_of_nonneg_right hs hcx.le) hb.2) ?_
  simp only [tanUpNeg, toReal_maximum]
  exact max_le_max (div_le_divUp _ _ hcl) (div_le_divUp _ _ hcu)

/-- `piBelow` is below `π`. -/
theorem piBelow_lt_pi : -- --- CONCL ---
    toReal (piBelow : 𝕋) < Real.pi := by -- --- PROOF ---
  have h1 := addDown_le_add (one : 𝕋) one
  have h2 := addDown_le_add (one : 𝕋) (addDown one one)
  have h3 := addDown_le_add (addDown (one : 𝕋) (addDown one one)) (half (half (half (one : 𝕋))))
  have e : toReal (half (half (half (one : 𝕋)))) = 1 / 8 := by
    simp only [toReal_half, toReal_one]; norm_num
  have h4 := Real.pi_gt_d2
  rw [piBelow]
  rw [e] at h3
  rw [toReal_one] at h1 h2
  norm_num at h4 ⊢
  linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
