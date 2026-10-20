module

public import Mathlib.Analysis.Normed.Lp.PiLp

@[expose] public section

/-!
# The `q`-norm is monotone in the absolute values

`|aᵢ| ≤ bᵢ` for all `i` gives `‖a‖_q ≤ ‖b‖_q`, for every `q ≥ 1` including `∞`.

## Inputs
* `q` – exponent
* `a` – first vector
* `b` – second vector

## Hypotheses
* `h` – each entry of the first vector is bounded by the second in absolute value

## Conclusion
* the norm of the first vector is at most that of the second
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped ENNReal

variable {l : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The `q`-norm is monotone in the absolute values of the entries. -/
theorem PiLp.norm_toLp_le_of_abs_le (q : ℝ≥0∞) [Fact (1 ≤ q)] (a b : Fin l → ℝ)
    (h : ∀ i, |a i| ≤ b i) : -- --- CONCL ---
    ‖WithLp.toLp q a‖ ≤ ‖WithLp.toLp q b‖ := by -- --- PROOF ---
  have hb : ∀ i, 0 ≤ b i := fun i => (abs_nonneg _).trans (h i)
  by_cases hq : q = ∞
  · subst hq
    simp only [PiLp.norm_toLp]
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => ?_
    rw [Real.norm_eq_abs]
    exact (h i).trans ((le_abs_self _).trans (by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm b i))
  · have hq0 : 0 < q.toReal :=
      ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ q)).ne' hq
    rw [PiLp.norm_eq_sum hq0, PiLp.norm_eq_sum hq0]
    refine Real.rpow_le_rpow (Finset.sum_nonneg fun i _ => by positivity)
      (Finset.sum_le_sum fun i _ => ?_) (by positivity)
    simp only [Real.norm_eq_abs]
    exact Real.rpow_le_rpow (abs_nonneg _) ((h i).trans (le_abs_self _)) hq0.le

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
