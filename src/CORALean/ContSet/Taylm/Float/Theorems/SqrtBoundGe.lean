import CORALean.ContSet.Taylm.Float.Operations.SqrtBound
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# `Taylm.sqrtBound` bounds the derivative of `√`

`√ = x^(1/2)`, so `√⁽ᴺ⁺¹⁾ ξ = ∏ᵢ(1/2 - i) · ξ^(1/2 - (N+1))` (`Real.iter_deriv_rpow_const`), the
product `sqrtDeriv (N+1) / 2ᴺ⁺¹` (`eval_descPochhammer_half`), and a negative power decreases, so
`ξ ≥ m₀` is bounded by `m₀^(1/2 - (N+1)) = √m₀ · (1/m₀)ᴺ⁺¹`. Each factor is below its rounding.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.sqrtBound_ge (q : ℕ) (m₀ : 𝕋) (hm : 0 < toReal m₀) (N : ℕ) {ξ : ℝ}
    (hξ : toReal m₀ ≤ ξ) :
    |iteratedDeriv (N + 1) Real.sqrt ξ| ≤ toReal (Taylm.sqrtBound q m₀ N) := by -- --- PROOF ---
  have hξ0 : 0 < ξ := lt_of_lt_of_le hm hξ
  have hfun : Real.sqrt = fun x : ℝ => x ^ (1 / 2 : ℝ) := funext Real.sqrt_eq_rpow
  rw [hfun, iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const, abs_mul,
    abs_of_pos (Real.rpow_pos_of_pos hξ0 _)]
  have hz : (1 / 2 : ℝ) - ((N + 1 : ℕ) : ℝ) ≤ 0 := by
    have : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos _
    linarith
  refine le_trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hm hξ hz)
    (abs_nonneg _)) ?_
  -- the three factors
  have hpow : toReal m₀ ^ ((1 / 2 : ℝ) - ((N + 1 : ℕ) : ℝ)) =
      √(toReal m₀) * (1 / toReal m₀) ^ (N + 1) := by
    rw [Real.rpow_sub hm, Real.rpow_natCast, Real.sqrt_eq_rpow, one_div_pow, div_eq_mul_one_div]
  rw [hpow, eval_descPochhammer_half, abs_div, abs_pow, abs_two, ← mul_assoc]
  have hI := (intDown_le_intUp (𝕋 := 𝕋) |sqrtDeriv (N + 1)|).2
  rw [Int.cast_abs] at hI
  have ha : |(sqrtDeriv (N + 1) : ℝ)| / 2 ^ (N + 1) ≤
      toReal (halfPow (N + 1) (intUp |sqrtDeriv (N + 1)| : 𝕋)) := by
    rw [toReal_halfPow]; exact div_le_div_of_nonneg_right hI (by positivity)
  have hb := le_sqrtUp q m₀
  have hdiv := div_le_divUp (one : 𝕋) m₀ hm
  rw [toReal_one] at hdiv
  have hc := le_powUp (by positivity : (0 : ℝ) ≤ 1 / toReal m₀) hdiv (N + 1)
  have ha0 : 0 ≤ |(sqrtDeriv (N + 1) : ℝ)| / 2 ^ (N + 1) := by positivity
  refine le_trans ?_ (mul_le_mulUp _ _)
  refine mul_le_mul (le_trans ?_ (mul_le_mulUp _ _)) hc (by positivity)
    (le_trans (mul_nonneg ha0 (Real.sqrt_nonneg _)) (le_trans (mul_le_mul ha hb
      (Real.sqrt_nonneg _) (le_trans ha0 ha)) (mul_le_mulUp _ _)))
  exact mul_le_mul ha hb (Real.sqrt_nonneg _) (le_trans ha0 ha)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
