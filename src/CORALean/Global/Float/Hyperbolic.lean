import CORALean.Global.Float.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# `sinh`, `cosh` and `tanh` rounded in either direction

All three are built on `expUp`/`expDown` and exact halving, and need no division but one.

* `sinh x = (eˣ - e⁻ˣ)/2`: from above the first exponential is rounded up and the second down, so
  the upward bound needs `expUp` at `x` and the downward one `expUp` at `-x`.
* `cosh x = (eˣ + e⁻ˣ)/2`: both exponentials are rounded the same way, so the upward bound needs
  both `x ≤ 2ᵖ/2` and `-x ≤ 2ᵖ/2`, and the downward one needs nothing.
* `tanh x = 1 - 2/(e²ˣ + 1)`, increasing in `e²ˣ = (eˣ)²`, which is the square of the one
  exponential. The reciprocal is taken of `(E + 1)/2`, so no `two` is needed. The upward bound
  needs `x ≤ 2ᵖ/2`; the downward one nothing.

`expUp`'s range is therefore an explicit hypothesis on `x` wherever it is used, and `expDown` is
total, as in `Global/Float/Exp`. `p` is the exponential's precision.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋]


/-- `sinh x` from above: `(eˣ - e⁻ˣ)/2`, the first exponential up and the second down. -/
def sinhUp (p : ℕ) (x : 𝕋) : 𝕋 := half (subUp (expUp p x) (expDown p (neg x)))

/-- `sinh x` from below. -/
def sinhDown (p : ℕ) (x : 𝕋) : 𝕋 := half (subDown (expDown p x) (expUp p (neg x)))

/-- `cosh x` from above: `(eˣ + e⁻ˣ)/2`, both exponentials up. -/
def coshUp (p : ℕ) (x : 𝕋) : 𝕋 := half (addUp (expUp p x) (expUp p (neg x)))

/-- `cosh x` from below. -/
def coshDown (p : ℕ) (x : 𝕋) : 𝕋 := half (addDown (expDown p x) (expDown p (neg x)))

/-- `tanh x` from above: `1 - 2/(E + 1)` with `E ≥ e²ˣ`, the square of `expUp`. -/
def tanhUp (p : ℕ) (x : 𝕋) : 𝕋 :=
  let E := mulUp (expUp p x) (expUp p x)
  subUp one (divDown one (half (addUp E one)))

/-- `tanh x` from below: `E ≤ e²ˣ` is the square of `expDown`, and the divisor is floored at `1/2`
(its true value is at least that), so the reciprocal is defined. -/
def tanhDown (p : ℕ) (x : 𝕋) : 𝕋 :=
  let E := mulDown (expDown p x) (expDown p x)
  subDown one (divUp one (half (maximum one (addDown E one))))

variable [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The hyperbolic tangent through the exponential: `tanh x = 1 - 2/((eˣ)² + 1)`. -/
private theorem tanh_eq_one_sub (x : ℝ) :
    Real.tanh x = 1 - 2 / (Real.exp x ^ 2 + 1) := by
  have hu : 0 < Real.exp x := Real.exp_pos x
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq, Real.exp_neg]
  field_simp
  ring

theorem sinhUp_ge (p : ℕ) (x : 𝕋) (hx : toReal x ≤ 2 ^ p / 2) :
    Real.sinh (toReal x) ≤ toReal (sinhUp p x) := by -- --- PROOF ---
  have h1 := le_expUp p x hx
  have h2 := expDown_le p (neg x)
  have h3 := sub_le_subUp (expUp p x) (expDown p (neg x))
  rw [toReal_neg] at h2
  rw [sinhUp, toReal_half, Real.sinh_eq]
  linarith

theorem sinhDown_le (p : ℕ) (x : 𝕋) (hx : -toReal x ≤ 2 ^ p / 2) :
    toReal (sinhDown p x) ≤ Real.sinh (toReal x) := by -- --- PROOF ---
  have h1 := expDown_le p x
  have h2 := le_expUp p (neg x) (by rwa [toReal_neg])
  have h3 := subDown_le_sub (expDown p x) (expUp p (neg x))
  rw [toReal_neg] at h2
  rw [sinhDown, toReal_half, Real.sinh_eq]
  linarith

theorem coshUp_ge (p : ℕ) (x : 𝕋) (hx : toReal x ≤ 2 ^ p / 2) (hnx : -toReal x ≤ 2 ^ p / 2) :
    Real.cosh (toReal x) ≤ toReal (coshUp p x) := by -- --- PROOF ---
  have h1 := le_expUp p x hx
  have h2 := le_expUp p (neg x) (by rwa [toReal_neg])
  have h3 := add_le_addUp (expUp p x) (expUp p (neg x))
  rw [toReal_neg] at h2
  rw [coshUp, toReal_half, Real.cosh_eq]
  linarith

theorem coshDown_le (p : ℕ) (x : 𝕋) :
    toReal (coshDown p x) ≤ Real.cosh (toReal x) := by -- --- PROOF ---
  have h1 := expDown_le p x
  have h2 := expDown_le p (neg x)
  have h3 := addDown_le_add (expDown p x) (expDown p (neg x))
  rw [toReal_neg] at h2
  rw [coshDown, toReal_half, Real.cosh_eq]
  linarith

theorem tanhUp_ge (p : ℕ) (x : 𝕋) (hx : toReal x ≤ 2 ^ p / 2) :
    Real.tanh (toReal x) ≤ toReal (tanhUp p x) := by -- --- PROOF ---
  have hu := Real.exp_pos (toReal x)
  have h1 := le_expUp p x hx
  have h2 := mul_le_mulUp (expUp p x) (expUp p x)
  -- `E` is the square of an upper bound, so above `(eˣ)²`
  have hE : Real.exp (toReal x) ^ 2 ≤ toReal (mulUp (expUp p x) (expUp p x)) := by
    nlinarith
  have h3 := add_le_addUp (mulUp (expUp p x) (expUp p x)) (one : 𝕋)
  rw [toReal_one] at h3
  -- the halved denominator is positive
  have hd : 0 < toReal (half (addUp (mulUp (expUp p x) (expUp p x)) one)) := by
    rw [toReal_half]; nlinarith [sq_nonneg (Real.exp (toReal x))]
  have h4 := divDown_le_div (one : 𝕋) _ hd
  have h5 := sub_le_subUp (one : 𝕋)
    (divDown one (half (addUp (mulUp (expUp p x) (expUp p x)) one)))
  rw [toReal_half] at hd h4
  rw [toReal_one] at h4 h5
  -- the reciprocal of the halved denominator is below `2 / ((eˣ)² + 1)`
  have h6 : 1 / ((toReal (addUp (mulUp (expUp p x) (expUp p x)) one)) / 2) ≤
      2 / (Real.exp (toReal x) ^ 2 + 1) := by
    rw [one_div_div]
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  rw [tanhUp, tanh_eq_one_sub]
  linarith

theorem tanhDown_le (p : ℕ) (x : 𝕋) :
    toReal (tanhDown p x) ≤ Real.tanh (toReal x) := by -- --- PROOF ---
  have hu := Real.exp_pos (toReal x)
  have h0 := expDown_nonneg p x
  have h1 := expDown_le p x
  have h2 := mulDown_le_mul (expDown p x) (expDown p x)
  -- `E` is the square of a lower bound, so below `(eˣ)²`
  have hE : toReal (mulDown (expDown p x) (expDown p x)) ≤ Real.exp (toReal x) ^ 2 := by
    nlinarith
  have h3 := addDown_le_add (mulDown (expDown p x) (expDown p x)) (one : 𝕋)
  rw [toReal_one] at h3
  -- the floored denominator is between `1` and the true one
  have hm : toReal (maximum one (addDown (mulDown (expDown p x) (expDown p x)) one)) ≤
      Real.exp (toReal x) ^ 2 + 1 := by
    rw [toReal_maximum, toReal_one]
    exact max_le (by nlinarith [sq_nonneg (Real.exp (toReal x))]) (by linarith)
  have hm1 : 1 ≤ toReal (maximum one (addDown (mulDown (expDown p x) (expDown p x)) one)) := by
    rw [toReal_maximum, toReal_one]; exact le_max_left _ _
  have hd : 0 <
      toReal (half (maximum one (addDown (mulDown (expDown p x) (expDown p x)) one))) := by
    rw [toReal_half]; linarith
  have h4 := div_le_divUp (one : 𝕋) _ hd
  have h5 := subDown_le_sub (one : 𝕋)
    (divUp one (half (maximum one (addDown (mulDown (expDown p x) (expDown p x)) one))))
  rw [toReal_half] at hd h4
  rw [toReal_one] at h4 h5
  -- the reciprocal of the halved floored denominator is above `2 / ((eˣ)² + 1)`
  have h6 : 2 / (Real.exp (toReal x) ^ 2 + 1) ≤
      1 / (toReal (maximum one (addDown (mulDown (expDown p x) (expDown p x)) one)) / 2) := by
    rw [one_div_div]
    exact div_le_div_of_nonneg_left (by norm_num) (by linarith) hm
  rw [tanhDown, tanh_eq_one_sub]
  linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
