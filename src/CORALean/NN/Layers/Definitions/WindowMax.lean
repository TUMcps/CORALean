import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic

/-!
# The largest coordinate a pooling window reads

What max pooling computes, over ℝ: a supremum, which is what the layer encloses and never
what it runs. `k + 1` in the type is what says a pooling window is nonempty, which is what makes
a maximum exist at all.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The largest coordinate a window reads. -/
noncomputable def windowMax {k : ℕ} (f : Fin (k + 1) → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty f

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
