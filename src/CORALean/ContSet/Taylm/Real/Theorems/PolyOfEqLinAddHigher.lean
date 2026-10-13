import CORALean.ContSet.Taylm.Real.Operations.LinCoef
import CORALean.ContSet.Taylm.Real.Operations.HigherTerms
import CORALean.ContSet.Taylm.Real.Theorems.DegreeEqOne
import CORALean.ContSet.Taylm.Real.Theorems.DegreeSingle

/-!
# A polynomial as constant, linear and higher part

`P(s) = c + Σₖ Lₖ sₖ + P_{≥2}(s)`: every term has degree zero (a constant), one (a coordinate,
`degree_eq_one`) or more. The split [1, Sec. 2] bounds the linear and the nonlinear part by.

## References

* [1] K. Makino and M. Berz. "Verified Global Optimization with Taylor Model-based Range
      Bounders". Transactions on Computers, 11(4):1611-1618, 2005.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.polyOf_eq_lin_add_higher (L : List (ℝ × (Fin n → ℕ))) (s : Vec ℝ n) :
    Taylm.polyOf L s = ((L.filter fun a => Taylm.degree a.2 == 0).map Prod.fst).sum
      + ∑ k, Taylm.linCoef L k * s k + Taylm.polyOf (Taylm.higherTerms L) s := by -- --- PROOF ---
  induction L with
  | nil => simp [Taylm.linCoef, Taylm.higherTerms]
  | cons a L ih =>
    -- how each of the three parts grows by one term
    have hc : ((a :: L).filter fun a => Taylm.degree a.2 == 0).map Prod.fst
        = (if Taylm.degree a.2 = 0 then [a.1] else []) ++
          (L.filter fun a => Taylm.degree a.2 == 0).map Prod.fst := by
      by_cases h : Taylm.degree a.2 = 0 <;> simp [h]
    have hl : ∀ k, Taylm.linCoef (a :: L) k
        = (if a.2 = Pi.single k 1 then a.1 else 0) + Taylm.linCoef L k := by
      intro k
      by_cases h : a.2 = Pi.single k 1 <;> simp [Taylm.linCoef, h]
    have hh : Taylm.polyOf (Taylm.higherTerms (a :: L)) s
        = (if 2 ≤ Taylm.degree a.2 then a.1 * Taylm.monomial a.2 s else 0)
          + Taylm.polyOf (Taylm.higherTerms L) s := by
      by_cases h : 2 ≤ Taylm.degree a.2 <;> simp [Taylm.higherTerms, h]
    rw [Taylm.polyOf_cons, ih, hc, hh, List.sum_append]
    simp only [hl, add_mul, Finset.sum_add_distrib]
    rcases Nat.lt_or_ge (Taylm.degree a.2) 2 with hd | hd
    · rcases Nat.lt_or_ge (Taylm.degree a.2) 1 with hd0 | hd1
      -- a constant term: its monomial is one
      · have h0 : Taylm.degree a.2 = 0 := by omega
        have he : a.2 = 0 := funext fun k =>
          (Finset.sum_eq_zero_iff.1 h0) k (Finset.mem_univ k)
        have hns : ∀ k, a.2 ≠ Pi.single k 1 := fun k h => by
          have := Taylm.degree_single k; rw [← h, h0] at this; exact zero_ne_one this
        have hm : Taylm.monomial a.2 s = 1 := by rw [he, Taylm.monomial_zero]
        simp only [if_pos h0, hns, if_false, zero_mul, Finset.sum_const_zero,
          show ¬ (2 ≤ Taylm.degree a.2) by omega, hm, List.sum_cons, List.sum_nil]
        ring
      -- a linear term: its monomial is its variable
      · have h1 : Taylm.degree a.2 = 1 := by omega
        obtain ⟨k, hk⟩ := Taylm.degree_eq_one h1
        have hsum : ∑ j, (if a.2 = Pi.single j 1 then a.1 else 0) * s j = a.1 * s k := by
          rw [Finset.sum_eq_single k]
          · simp [hk]
          · intro j _ hj
            have : a.2 ≠ Pi.single j 1 := by
              rw [hk]; intro he
              have := congrFun he k
              simp [Ne.symm hj] at this
            simp [this]
          · simp
        rw [hsum, if_neg (show ¬ (2 ≤ Taylm.degree a.2) by omega),
          if_neg (show Taylm.degree a.2 ≠ 0 by omega), hk, Taylm.monomial_single]
        simp only [List.sum_nil]
        ring
    -- a higher term: it stays among the higher ones
    · have hns : ∀ k, a.2 ≠ Pi.single k 1 := fun k h => by
        have := Taylm.degree_single k; rw [← h] at this; omega
      simp only [hns, if_false, zero_mul, Finset.sum_const_zero, if_pos hd,
        if_neg (show Taylm.degree a.2 ≠ 0 by omega), List.sum_nil]
      ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
