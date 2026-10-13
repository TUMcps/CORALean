module

public import CORALean.ContSet.Taylm.Real.Operations.ConstCoef
public import CORALean.ContSet.Taylm.Real.Definitions.Scaled
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# The constant part is at most the weight

`constCoef` sums the coefficients of degree zero, whose weight is their magnitude.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.abs_constCoef_le (T : Taylm n) {h : ℝ} (h0 : 0 < h) :
    |T.constCoef| ≤ Taylm.weight T.terms h := by -- --- PROOF ---
  unfold Taylm.constCoef
  induction T.terms with
  | nil => simp [Taylm.weight]
  | cons a L ih =>
    have hw : 0 ≤ |a.1| / h ^ Taylm.degree a.2 := div_nonneg (abs_nonneg _) (pow_pos h0 _).le
    simp only [Taylm.weight, List.map_cons, List.sum_cons, List.filter_cons] at ih ⊢
    split_ifs with hd
    · simp only [beq_iff_eq] at hd
      simp only [List.map_cons, List.sum_cons, hd, pow_zero, div_one]
      exact le_trans (abs_add_le _ _) (add_le_add le_rfl ih)
    · linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
