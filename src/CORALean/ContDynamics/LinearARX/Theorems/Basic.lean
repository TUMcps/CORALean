module

public import CORALean.ContDynamics.LinearARX.LinearARX

@[expose] public section

/-!
# `ContDynamics/LinearARX/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean

variable {dy p : ℕ}


-- ==================================  `LinearARX.sum_block`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A sum over the coordinates of `Vec ℝ (p * dy)` is the sum over blocks of the sum
over the coordinates inside, by `finProdFinEquiv`. -/
theorem LinearARX.sum_block (f : Fin (p * dy) → ℝ) :
    ∑ c, f c = ∑ a : Fin p, ∑ b : Fin dy, f (finProdFinEquiv (a, b)) := by
  rw [← Fintype.sum_prod_type', ← finProdFinEquiv.sum_comp]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
