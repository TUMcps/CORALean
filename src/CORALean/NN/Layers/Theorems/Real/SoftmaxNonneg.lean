import CORALean.NN.Layers.Theorems.Real.ExpSumPos

/-!
# Softmax is nonnegative

A positive numerator over a positive denominator.
-/

-- Authors:       Tobias Ladner
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem softmax_nonneg (x : Vec ℝ n) (i : Fin n) : 0 ≤ softmax x i :=
  div_nonneg (Real.exp_pos (x i)).le (exp_sum_pos x i).le

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
