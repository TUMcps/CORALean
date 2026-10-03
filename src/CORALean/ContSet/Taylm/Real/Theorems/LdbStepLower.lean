import CORALean.ContSet.Taylm.Real.Operations.LdbStep
import CORALean.ContSet.Taylm.Real.Theorems.PolyOfEqLinAddHigher
import CORALean.ContSet.Taylm.Real.Theorems.PolyBoundsMem

/-!
# The LDB lower end is a lower bound

`M = c - Σ|Lₖ| + l(P_{≥2}) + l(I)` is below the enclosed function on the normalized box,
[1, Sec. 2]: the linear part is at least `-Σ|Lₖ|` there.

## References

* [1] K. Makino and M. Berz. "Verified Global Optimization with Taylor Model-based Range
      Bounders". Transactions on Computers, 11(4):1611-1618, 2005.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.ldbStep_lower {T : Taylm n} {g : Vec ℝ n → ℝ} (h : T.Encloses g) {s : Vec ℝ n}
    (hs : s ∈ Taylm.box n) : T.ldbStep.1 ≤ g s := by -- --- PROOF ---
  have hr := h s hs
  have hdec := Taylm.polyOf_eq_lin_add_higher T.terms s
  have hb := Taylm.polyBounds_mem (Taylm.higherTerms T.terms) hs
  have hlin : -∑ k, |Taylm.linCoef T.terms k| ≤ ∑ k, Taylm.linCoef T.terms k * s k := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun k _ => ?_
    have := abs_le.1 (hs k)
    have h1 := neg_abs_le (Taylm.linCoef T.terms k * s k)
    rw [abs_mul] at h1
    nlinarith [abs_nonneg (Taylm.linCoef T.terms k), abs_nonneg (s k), abs_le.2 this]
  simp only [Taylm.ldbStep, Taylm.poly, Taylm.constCoef] at hr ⊢
  linarith [hr.1, hb.1]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
