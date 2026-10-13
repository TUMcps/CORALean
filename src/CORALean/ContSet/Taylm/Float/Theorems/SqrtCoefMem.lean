module

public import CORALean.ContSet.Taylm.Float.Operations.SqrtCoef
public import CORALean.ContSet.Interval.Float.Theorems.MulLoLe
public import CORALean.ContSet.Interval.Float.Theorems.LeMulHi
public import CORALean.ContSet.Interval.Real.Theorems.MulBetweenCorners
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

/-!
# `Taylm.sqrtCoef` encloses the coefficient of `√`

`√⁽ᵏ⁾ c / k! = (sqrtDeriv k / 2ᵏ) · √c · (1/c)ᵏ · (1 / k!)` for `c > 0`
(`Real.iter_deriv_rpow_const`, `eval_descPochhammer_half`), each factor between its enclosure
(`intDown_le_intUp`, `toReal_halfPow`, `sqrtDown_le`/`le_sqrtUp`, `powDown_le`/`le_powUp`,
`divFact_mem`), the four through `mul_between_corners`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.sqrtCoef_mem (q : ℕ) (c : 𝕋) (hc : 0 < toReal c) (k : ℕ) :
    toReal (Taylm.sqrtCoef q c k).1 ≤
        iteratedDeriv k Real.sqrt (toReal c) / (k.factorial : ℝ) ∧
      iteratedDeriv k Real.sqrt (toReal c) / (k.factorial : ℝ) ≤
        toReal (Taylm.sqrtCoef q c k).2 := by -- --- PROOF ---
  -- the derivative as a product of the four factors
  have hfun : Real.sqrt = fun x : ℝ => x ^ (1 / 2 : ℝ) := funext Real.sqrt_eq_rpow
  have hd : iteratedDeriv k Real.sqrt (toReal c) / (k.factorial : ℝ) =
      ((sqrtDeriv k : ℝ) / 2 ^ k * √(toReal c)) * (1 / toReal c) ^ k *
        (1 / (k.factorial : ℝ)) := by
    rw [hfun, iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const, eval_descPochhammer_half,
      Real.rpow_sub hc, Real.rpow_natCast, one_div_pow, div_eq_mul_one_div]
    have hs : toReal c ^ (1 / 2 : ℝ) = √(toReal c) := (Real.sqrt_eq_rpow _).symm
    dsimp only
    rw [hs]
    ring
  -- the factors
  have hI := intDown_le_intUp (𝕋 := 𝕋) (sqrtDeriv k)
  have hDh : toReal (halfPow k (intDown (sqrtDeriv k) : 𝕋)) ≤ (sqrtDeriv k : ℝ) / 2 ^ k ∧
      (sqrtDeriv k : ℝ) / 2 ^ k ≤ toReal (halfPow k (intUp (sqrtDeriv k) : 𝕋)) := by
    rw [toReal_halfPow, toReal_halfPow]
    exact ⟨div_le_div_of_nonneg_right hI.1 (by positivity),
      div_le_div_of_nonneg_right hI.2 (by positivity)⟩
  -- `1 / c` between its roundings, and the powers
  have hdiv1 := div_le_divUp (one : 𝕋) c hc
  have hdiv2 := divDown_le_div (one : 𝕋) c hc
  rw [toReal_one] at hdiv1 hdiv2
  have hw0 : (0 : ℝ) ≤ toReal (maximum zero (divDown one c)) := by
    rw [toReal_maximum, toReal_zero]; exact le_max_left _ _
  have hwl : toReal (maximum zero (divDown one c)) ≤ 1 / toReal c := by
    rw [toReal_maximum, toReal_zero]; exact max_le (by positivity) hdiv2
  have hpl := powDown_le hw0 hwl k
  have hph := le_powUp (by positivity : (0 : ℝ) ≤ 1 / toReal c) hdiv1 k
  have hG := divFact_mem ((one : 𝕋), (one : 𝕋)) zero_le_one
    (by rw [toReal_one]; exact ⟨le_rfl, le_rfl⟩) k
  -- the four factors through the corner products
  have hA := Real.Interval.mul_between_corners hDh.1 hDh.2 (sqrtDown_le q c) (le_sqrtUp q c)
  have hB := Real.Interval.mul_between_corners
    (le_trans (Interval.mulLo_le _ _ _ _) hA.1) (le_trans hA.2 (Interval.le_mulHi _ _ _ _))
    hpl hph
  have hC := Real.Interval.mul_between_corners
    (le_trans (Interval.mulLo_le _ _ _ _) hB.1) (le_trans hB.2 (Interval.le_mulHi _ _ _ _))
    (hG.1) (hG.2)
  rw [hd]
  exact ⟨le_trans (Interval.mulLo_le _ _ _ _) hC.1, le_trans hC.2 (Interval.le_mulHi _ _ _ _)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
