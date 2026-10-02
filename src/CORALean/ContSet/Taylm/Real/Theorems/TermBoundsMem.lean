import CORALean.ContSet.Taylm.Real.Operations.TermBounds
import Mathlib.Tactic.Linarith

/-!
# One term stays in `termBounds` on the box

The three cases of CORA's `aux_intPower`: a zero exponent is the constant itself, an
all-even one a monomial in `[0, 1]`, any other one in `[-1, 1]`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.termBounds_mem (a : ℝ × (Fin n → ℕ)) {t : Vec ℝ n} (ht : t ∈ Taylm.box n) :
    (Taylm.termBounds a).1 ≤ a.1 * Taylm.monomial a.2 t ∧
      a.1 * Taylm.monomial a.2 t ≤ (Taylm.termBounds a).2 := by -- --- PROOF ---
  have hm := abs_le.1 (Taylm.abs_monomial_le_one ht a.2)
  unfold Taylm.termBounds
  split_ifs with h0 hev
  · -- degree zero: every exponent is zero, the monomial is one
    have : a.2 = 0 := funext fun k => (Finset.sum_eq_zero_iff.1 h0) k (Finset.mem_univ k)
    simp [this, Taylm.monomial_zero]
  · -- all even: the monomial is in `[0, 1]`
    have hnn : 0 ≤ Taylm.monomial a.2 t :=
      Finset.prod_nonneg fun k _ => (hev k).pow_nonneg _
    constructor
    · rcases le_total a.1 0 with ha | ha
      · rw [min_eq_left ha]; nlinarith
      · rw [min_eq_right ha]; exact mul_nonneg ha hnn
    · rcases le_total a.1 0 with ha | ha
      · rw [max_eq_right ha]; exact mul_nonpos_of_nonpos_of_nonneg ha hnn
      · rw [max_eq_left ha]; nlinarith
  · -- otherwise only `|monomial| ≤ 1` is known
    have := abs_le.1 (show |a.1 * Taylm.monomial a.2 t| ≤ |a.1| by
      rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Taylm.abs_monomial_le_one ht _))
    exact ⟨this.1, this.2⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
