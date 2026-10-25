module

public import Mathlib.Analysis.Normed.Lp.PiLp

@[expose] public section

/-!
# Hölder's inequality for the `q`-norms on `ℝᵏ`

`Σ aᵢ bᵢ ≤ ‖a‖_{q*} ‖b‖_q` for `q ∈ [1, ∞]` and `q*` its Hölder conjugate, the endpoints
`q = 1, ∞` included, with the norms those of `PiLp`. Used by the Gaussian rounding of
[1, Thm. 15 (accuracy)], [1, Thm. 17] and [1, Thm. 19]; the open range is
`Real.inner_le_Lp_mul_Lq`.

## Inputs
* `k` – dimension
* `q` – exponent
* `q'` – its conjugate exponent
* `a` – first vector
* `b` – second vector

## Hypotheses
* none

## Conclusion
* the sum of products is at most the product of the dual norms

## References

* [1] A. Kulmburg, L. Schäfer and M. Althoff. "Approximability of the Containment Problem for
      Zonotopes and Ellipsotopes". IEEE Transactions on Automatic Control, 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped ENNReal


-- =======================================  MAIN THEOREM  ======================================= --

theorem piLp_sum_mul_le_norm_mul_norm {k : ℕ} (q q' : ℝ≥0∞) [Fact (1 ≤ q)] [q.HolderConjugate q']
    (a b : Fin k → ℝ) : -- --- CONCL ---
    ∑ i, a i * b i ≤ ‖WithLp.toLp q' a‖ * ‖WithLp.toLp q b‖ := by -- --- PROOF ---
  -- `q = ∞`, `q' = 1`: termwise
  by_cases hq : q = ∞
  · have hq' : q' = 1 := (ENNReal.HolderConjugate.eq_top_iff_eq_one q q').mp hq
    subst hq hq'
    rw [PiLp.norm_eq_of_L1, PiLp.norm_toLp, Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    simp only [Real.norm_eq_abs]
    calc a i * b i ≤ |a i| * |b i| := by rw [← abs_mul]; exact le_abs_self _
      _ ≤ |a i| * ‖b‖ := mul_le_mul_of_nonneg_left
          (by simpa [Real.norm_eq_abs] using norm_le_pi_norm b i) (abs_nonneg _)
  -- `q = 1`, `q' = ∞`: termwise
  by_cases hq1 : q = 1
  · have hq' : q' = ∞ := (ENNReal.HolderConjugate.eq_top_iff_eq_one q' q).mpr hq1
    subst hq1 hq'
    rw [PiLp.norm_eq_of_L1, PiLp.norm_toLp, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    simp only [Real.norm_eq_abs]
    calc a i * b i ≤ |a i| * |b i| := by rw [← abs_mul]; exact le_abs_self _
      _ ≤ ‖a‖ * |b i| := mul_le_mul_of_nonneg_right
          (by simpa [Real.norm_eq_abs] using norm_le_pi_norm a i) (abs_nonneg _)
  -- `1 < q < ∞`: the real Hölder inequality
  · have hq'1 : q' ≠ ∞ := (ENNReal.HolderConjugate.ne_top_iff_ne_one q' q).mpr hq1
    have hq0 : 0 < q.toReal :=
      ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ q)).ne' hq
    have hq'0 : 0 < q'.toReal :=
      ENNReal.toReal_pos (ENNReal.HolderConjugate.ne_zero q' q) hq'1
    have hR : q'.toReal.HolderConjugate q.toReal := by
      simpa using ENNReal.HolderTriple.toReal 1 hq'0 hq0
    rw [PiLp.norm_eq_sum hq'0, PiLp.norm_eq_sum hq0]
    simpa [Real.norm_eq_abs] using Real.inner_le_Lp_mul_Lq Finset.univ a b hR

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
