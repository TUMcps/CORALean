import CORALean.NN.Operations.MergeRowWeight

/-!
# A row weight is nonnegative

ℝ-only, the weights being exact: a sum of absolute values.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem mergeRowWeight_nonneg {n n₂ : ℕ} (W : Mat ℝ n₂ n) (i : Fin n₂) :
    0 ≤ mergeRowWeight W i :=
  Finset.sum_nonneg fun k _ => abs_nonneg (W i k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
