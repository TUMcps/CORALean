import CORALean.NN.Layers.Theorems.Real.SoftmaxEqInv

/-!
# Softmax above its raw lower bound

The denominator is largest at the box's opposite corner, which bounds softmax below. Over ℝ
alone: it asks for an upper bound on an exponential, which no machine scalar supplies totally.
-/

-- Authors:       Tobias Ladner
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


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

/-- And largest at the opposite corner, which is the lower bound on `softmax`. -/
theorem raw_le_softmax {lo hi x : Vec ℝ n} (hx : ∀ i, lo i ≤ x i ∧ x i ≤ hi i) (i : Fin n) :
    (1 + ∑ j ∈ Finset.univ.erase i, Real.exp (hi j - lo i))⁻¹ ≤ softmax x i := by -- --- PROOF ---
  have hmono : ∑ j ∈ Finset.univ.erase i, Real.exp (x j - x i)
      ≤ ∑ j ∈ Finset.univ.erase i, Real.exp (hi j - lo i) :=
    Finset.sum_le_sum fun j _ =>
      Real.exp_le_exp.mpr (by linarith [(hx j).2, (hx i).1])
  rw [softmax_eq_inv x i, inv_eq_one_div, inv_eq_one_div]
  exact one_div_le_one_div_of_le
    (aux_one_add_exp_sum_pos x i (x i)) (by linarith)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
