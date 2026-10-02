import CORALean.ContSet.Taylm.Float.Operations.LogCoef
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# `logCoef` encloses the Taylor coefficients of `log`

At a positive centre. `aux_log_coef` reads `log⁽ᵏ⁺¹⁾(c)/(k+1)!` as `(-1)ᵏ (1/c)ᵏ⁺¹/(k+1)`
off `iter_deriv_inv`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The Taylor coefficients of `log` at a positive point. -/
theorem Taylm.aux_log_coef {c : ℝ} (hc : 0 < c) (k : ℕ) :
    iteratedDeriv (k + 1) Real.log c / ((k + 1).factorial : ℝ)
      = (-1) ^ k * (1 / c) ^ (k + 1) / ((k + 1 : ℕ) : ℝ) := by -- --- PROOF ---
  rw [iteratedDeriv_succ', Real.deriv_log', iteratedDeriv_eq_iterate, iter_deriv_inv,
    show (-1 - (k : ℤ)) = -((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast,
    Nat.factorial_succ, Nat.cast_mul, one_div, inv_pow]
  have : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  field_simp


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.logCoef_mem (q s : ℕ) {c : 𝕋} (hc : 0 < toReal c) (k : ℕ) :
    toReal (Taylm.logCoef q s c k).1 ≤ iteratedDeriv k Real.log (toReal c) / (k.factorial : ℝ)
      ∧ iteratedDeriv k Real.log (toReal c) / (k.factorial : ℝ)
        ≤ toReal (Taylm.logCoef q s c k).2 := by -- --- PROOF ---
  have hinvU : 1 / toReal c ≤ toReal (divUp one c) := by
    have := div_le_divUp one c hc; rwa [toReal_one] at this
  have hinv0 : 0 < 1 / toReal c := by positivity
  cases k with
  | zero =>
    simp only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one, Taylm.logCoef,
      toReal_neg]
    constructor
    · -- `log c = -log (1/c) ≥ -log u ≥ -logUp u` for `u ≥ 1/c`
      have hu : 0 < toReal (divUp one c) := lt_of_lt_of_le hinv0 hinvU
      have h1 := le_logUp q s (divUp one c) hu
      have h2 := Real.log_le_log hinv0 hinvU
      rw [one_div, Real.log_inv] at h2
      linarith
    · exact le_logUp q s c hc
  | succ k =>
    rw [Taylm.aux_log_coef hc k]
    -- the magnitude `(1/c)^(k+1) / (k+1)` and its two roundings
    set m := (1 / toReal c) ^ (k + 1) / ((k + 1 : ℕ) : ℝ)
    have hk1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
    have hU : ((k + 1 : ℕ) : ℝ) * 1 ≤ toReal (nsmulUp (k + 1) (one : 𝕋)) := by
      have := le_nsmulUp (k + 1) (one : 𝕋); rwa [toReal_one] at this
    have hD : toReal (nsmulDown (k + 1) (one : 𝕋)) ≤ ((k + 1 : ℕ) : ℝ) * 1 := by
      have := nsmulDown_le (k + 1) (one : 𝕋); rwa [toReal_one] at this
    have hUpos : (0 : ℝ) < toReal (nsmulUp (k + 1) (one : 𝕋)) := by linarith
    have hm : toReal (maximum one (nsmulDown (k + 1) (one : 𝕋))) =
        max 1 (toReal (nsmulDown (k + 1) (one : 𝕋))) := by rw [toReal_maximum, toReal_one]
    have hm1 : (1 : ℝ) ≤ toReal (maximum one (nsmulDown (k + 1) (one : 𝕋))) := by
      rw [hm]; exact le_max_left _ _
    have hmk : toReal (maximum one (nsmulDown (k + 1) (one : 𝕋))) ≤ ((k + 1 : ℕ) : ℝ) := by
      rw [hm]; exact max_le hk1 (by linarith)
    -- the lower end of `1/c`, floored at zero so the downward power stays monotone
    have hpw0 : 0 ≤ (1 / toReal c) ^ (k + 1) := pow_nonneg hinv0.le _
    have hL0 : 0 ≤ toReal (maximum zero (divDown one c)) := by
      rw [toReal_maximum, toReal_zero]; exact le_max_left _ _
    have hL : toReal (maximum zero (divDown one c)) ≤ 1 / toReal c := by
      rw [toReal_maximum, toReal_zero]
      refine max_le hinv0.le ?_
      have := divDown_le_div one c hc; rwa [toReal_one] at this
    -- the two ends of the magnitude
    have hlo : toReal (divDown (powDown (maximum zero (divDown one c)) (k + 1))
        (nsmulUp (k + 1) one)) ≤ m := by
      refine le_trans (divDown_le_div _ _ hUpos) ?_
      calc toReal (powDown (maximum zero (divDown one c)) (k + 1))
            / toReal (nsmulUp (k + 1) (one : 𝕋))
          ≤ (1 / toReal c) ^ (k + 1) / toReal (nsmulUp (k + 1) (one : 𝕋)) :=
            div_le_div_of_nonneg_right (powDown_le hL0 hL _) hUpos.le
        _ ≤ m := div_le_div_of_nonneg_left hpw0 (by linarith) (by linarith)
    have hhi : m ≤ toReal (divUp (powUp (divUp one c) (k + 1))
        (maximum one (nsmulDown (k + 1) one))) := by
      refine le_trans ?_ (div_le_divUp _ _ (by linarith))
      calc m ≤ (1 / toReal c) ^ (k + 1) / toReal (maximum one (nsmulDown (k + 1) (one : 𝕋))) :=
            div_le_div_of_nonneg_left hpw0 (by linarith) hmk
        _ ≤ _ := div_le_div_of_nonneg_right (le_powUp hinv0.le hinvU _) (by linarith)
    -- the sign `(-1)^k`
    have hsplit : (-1 : ℝ) ^ k * (1 / toReal c) ^ (k + 1) / ((k + 1 : ℕ) : ℝ)
        = (-1) ^ k * m := by simp only [m]; ring
    rw [hsplit]
    simp only [Taylm.logCoef]
    rcases Nat.even_or_odd k with he | ho
    · rw [if_pos (Nat.even_iff.1 he), he.neg_one_pow, one_mul]
      exact ⟨hlo, hhi⟩
    · rw [if_neg (by rw [Nat.odd_iff.1 ho]; exact one_ne_zero), ho.neg_one_pow, toReal_neg,
        toReal_neg]
      constructor <;> linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
