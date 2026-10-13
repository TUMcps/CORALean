module

public import CORALean.NN.Layers.Theorems.Real.ExpSumPos

@[expose] public section

/-!
# Softmax's outputs sum to one

The constraint the enclosure is built to keep, and a fact a specification may use directly.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem softmax_sum_eq_one (x : Vec ℝ n) (i : Fin n) : ∑ j, softmax x j = 1 := by
  show ∑ j, Real.exp (x j) / (∑ k, Real.exp (x k)) = 1
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (exp_sum_pos x i))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
