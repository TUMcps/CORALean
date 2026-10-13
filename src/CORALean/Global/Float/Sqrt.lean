module

public import CORALean.Global.Float.EuclideanNorm
public import CORALean.Global.Float.SoundFloatArithmetic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-!
# A square root rounded in either direction

`EuclideanNorm` can only *check* a root a caller proposes. This file computes one, from
`FloatOps` alone: Newton's iteration `s ↦ (s + a/s)/2`, started above the root, with `p` steps.

Soundness does not depend on convergence. Every iterate is an upper bound of `√a`, by induction:
the start `(a + 1)/2` is one (AM-GM), and a Newton step from a positive `s` is one (AM-GM again,
with `divUp` and `addUp` rounding up). The step is only taken from an `s` that `ltStrict` proves
positive, so `div_le_divUp`'s one partial guarantee is met, and the `minimum` with the previous
iterate keeps the sequence from growing. More fuel buys accuracy only, as `n` does for `expUp`.

`sqrtDown a = a / sqrtUp a`, below `√a` because the divisor is above it; `zero` where the divisor
is not proven positive. The argument is floored at zero first, so there is no side condition.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋]


/-- One Newton step from `s`, taken only if `s` is provably positive, never growing. -/
def sqrtStep (a s : 𝕋) : 𝕋 :=
  if ltStrict zero s = true then minimum s (half (addUp s (divUp a s))) else s

/-- `p` steps. -/
def sqrtIter (a : 𝕋) : ℕ → 𝕋 → 𝕋
  | 0, s => s
  | k + 1, s => sqrtIter a k (sqrtStep a s)

/-- `√a` from above, at every `a`; `p` is the number of Newton steps. -/
def sqrtUp (p : ℕ) (a : 𝕋) : 𝕋 :=
  let a₀ := maximum zero a
  let s₀ := half (addUp a₀ one)
  sqrtIter a₀ p s₀

/-- `√a` from below, at every `a`. -/
def sqrtDown (p : ℕ) (a : 𝕋) : 𝕋 :=
  let a₀ := maximum zero a
  let s := sqrtUp p a
  if ltStrict zero s = true then divDown a₀ s else zero

/-- The Euclidean length of a vector held in `𝕋`, rounded up: `sqrtUp` of `sqSumUp` of the
magnitudes. -/
def normUp (p : ℕ) {k : ℕ} (m : Vec 𝕋 k) : 𝕋 := sqrtUp p (sqSumUp fun i => absolute (m i))

variable [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- AM-GM: `√a ≤ (s + a/s)/2` for a positive `s`. -/
private theorem sqrt_le_newton {a s : ℝ} (ha : 0 ≤ a) (hs : 0 < s) :
    Real.sqrt a ≤ (s + a / s) / 2 := by -- --- PROOF ---
  have hr := Real.sq_sqrt ha
  have hr0 := Real.sqrt_nonneg a
  have h1 : Real.sqrt a * (2 * s) ≤ s * s + a := by nlinarith [sq_nonneg (s - Real.sqrt a)]
  have h2 : s + a / s = (s * s + a) / s := by field_simp
  rw [h2, div_div, le_div_iff₀ (by positivity)]
  linarith

private theorem sqrt_max_zero (x : ℝ) : Real.sqrt (max 0 x) = Real.sqrt x := by
  rcases le_total 0 x with h | h
  · rw [max_eq_right h]
  · rw [max_eq_left h, Real.sqrt_zero, Real.sqrt_eq_zero_of_nonpos h]

private theorem sqrtStep_ge {a s : 𝕋} (ha : 0 ≤ toReal a) (h : Real.sqrt (toReal a) ≤ toReal s) :
    Real.sqrt (toReal a) ≤ toReal (sqrtStep a s) := by -- --- PROOF ---
  unfold sqrtStep
  split_ifs with hl
  · have hs : 0 < toReal s := by
      have := toReal_lt_of_ltStrict hl
      rwa [toReal_zero] at this
    -- AM-GM, then the roundings of the quotient and the sum
    have hnewton := sqrt_le_newton ha hs
    have hdiv := div_le_divUp a s hs
    have hadd := add_le_addUp s (divUp a s)
    rw [toReal_minimum, toReal_half]
    exact le_min h (by linarith)
  · exact h

private theorem sqrtIter_ge {a : 𝕋} (ha : 0 ≤ toReal a) :
    ∀ (k : ℕ) (s : 𝕋), Real.sqrt (toReal a) ≤ toReal s →
      Real.sqrt (toReal a) ≤ toReal (sqrtIter a k s) := by
  intro k
  induction k with
  | zero => exact fun s h => h
  | succ k ih => exact fun s h => ih _ (sqrtStep_ge ha h)

private theorem toReal_maximum_zero_nonneg (a : 𝕋) : 0 ≤ toReal (maximum zero a) := by
  rw [toReal_maximum, toReal_zero]
  exact le_max_left _ _

/-- The computed root is above the real one, whatever the fuel. -/
theorem le_sqrtUp (p : ℕ) (a : 𝕋) :
    Real.sqrt (toReal a) ≤ toReal (sqrtUp p a) := by -- --- PROOF ---
  have ha := toReal_maximum_zero_nonneg a
  have hsq : Real.sqrt (toReal (maximum zero a)) = Real.sqrt (toReal a) := by
    rw [toReal_maximum, toReal_zero, sqrt_max_zero]
  rw [← hsq]
  refine sqrtIter_ge ha p _ ?_
  have hr := Real.sq_sqrt ha
  have hadd := add_le_addUp (maximum zero a) one
  rw [toReal_one] at hadd
  rw [toReal_half]
  nlinarith [sq_nonneg (Real.sqrt (toReal (maximum zero a)) - 1)]

/-- The computed root from below is under the real one, whatever the fuel. -/
theorem sqrtDown_le (p : ℕ) (a : 𝕋) :
    toReal (sqrtDown p a) ≤ Real.sqrt (toReal a) := by -- --- PROOF ---
  have ha := toReal_maximum_zero_nonneg a
  have hsq : Real.sqrt (toReal (maximum zero a)) = Real.sqrt (toReal a) := by
    rw [toReal_maximum, toReal_zero, sqrt_max_zero]
  have hup := le_sqrtUp p a
  simp only [sqrtDown]
  split_ifs with hl
  · have hs : 0 < toReal (sqrtUp p a) := by
      have := toReal_lt_of_ltStrict hl
      rwa [toReal_zero] at this
    refine le_trans (divDown_le_div _ _ hs) ?_
    rw [div_le_iff₀ hs]
    have hr0 : 0 ≤ Real.sqrt (toReal a) := Real.sqrt_nonneg _
    have hrr : Real.sqrt (toReal a) * Real.sqrt (toReal a) = toReal (maximum zero a) := by
      rw [← hsq]; exact Real.mul_self_sqrt ha
    nlinarith
  · rw [toReal_zero]; exact Real.sqrt_nonneg _

theorem sqrtUp_nonneg (p : ℕ) (a : 𝕋) : 0 ≤ toReal (sqrtUp p a) :=
  le_trans (Real.sqrt_nonneg _) (le_sqrtUp p a)

/-- The norm of a vector known in magnitude is below the computed root of its squared length,
rounded up: `norm₂_le_of_sq_le` with the certificate computed. -/
theorem norm₂_le_sqrtUp {k : ℕ} {v : Vec ℝ k} {m : Vec 𝕋 k} (p : ℕ)
    (hm : ∀ j, |v j| ≤ toReal (m j)) :
    ‖v‖₂ ≤ toReal (sqrtUp p (sqSumUp m)) :=
  le_trans (Real.sqrt_le_sqrt (sq_sum_le_sqSumUp hm)) (le_sqrtUp p _)

/-- `normUp` bounds the norm of any real vector whose entries are within the stored ones in
magnitude, so the sign of a stored entry does not matter. -/
theorem norm₂_le_normUp {k : ℕ} {v : Vec ℝ k} {m : Vec 𝕋 k} (p : ℕ)
    (hm : ∀ j, |v j| ≤ |toReal (m j)|) : ‖v‖₂ ≤ toReal (normUp p m) :=
  norm₂_le_sqrtUp p fun j => by rw [toReal_absolute]; exact hm j

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
