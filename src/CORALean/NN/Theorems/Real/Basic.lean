module

public import CORALean.NN.Operations.MergeRowWeight
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

/-!
# `NN/Theorems/Real`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


-- =================================  `mergeRowWeight_nonneg`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       06-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---

namespace CORALean

/-- ℝ-only, the weights being exact: a sum of absolute values. -/
theorem mergeRowWeight_nonneg {n n₂ : ℕ} (W : Mat ℝ n₂ n) (i : Fin n₂) :
    0 ≤ mergeRowWeight W i :=
  Finset.sum_nonneg fun k _ => abs_nonneg (W i k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
