import CORALean.NN.Layers.Theorems.Real.SoftmaxEqInv

/-!
# Softmax below its raw upper bound

Each ratio `x j - x i` lies in `[lo j - hi i, hi j - lo i]`, and the denominator is monotone in
every one of them: smallest at the box's corner, which bounds softmax above.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem aux_one_add_exp_sum_pos (v : Vec ℝ n) (i : Fin n) (a : ℝ) :
    0 < 1 + ∑ j ∈ Finset.univ.erase i, Real.exp (v j - a) := by
  have h : (0:ℝ) ≤ ∑ j ∈ Finset.univ.erase i, Real.exp (v j - a) :=
    Finset.sum_nonneg fun j _ => (Real.exp_pos (v j - a)).le
  linarith


-- =======================================  MAIN THEOREM  ======================================= --

/-- The denominator is smallest when every ratio is, which is the box's corner. -/
theorem softmax_le_raw {lo hi x : Vec ℝ n} (hx : ∀ i, lo i ≤ x i ∧ x i ≤ hi i) (i : Fin n) :
    softmax x i ≤ (1 + ∑ j ∈ Finset.univ.erase i, Real.exp (lo j - hi i))⁻¹ := by -- --- PROOF ---
  have hmono : ∑ j ∈ Finset.univ.erase i, Real.exp (lo j - hi i)
      ≤ ∑ j ∈ Finset.univ.erase i, Real.exp (x j - x i) :=
    Finset.sum_le_sum fun j _ =>
      Real.exp_le_exp.mpr (by linarith [(hx j).1, (hx i).2])
  rw [softmax_eq_inv x i, inv_eq_one_div, inv_eq_one_div]
  exact one_div_le_one_div_of_le (aux_one_add_exp_sum_pos lo i (hi i)) (by linarith)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
