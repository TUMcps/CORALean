import CORALean.Global.Tensor
import Mathlib.Data.Real.Basic

/-!
# The set a classifier must avoid

The unsafe set a classification requirement is checked against: some label
other than the target at least ties it, so the target is not the unique
winner. Shared by `Robustness` and the sufficient-explanation theorems, which
state the same requirement over an abstract network's output.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Some label other than `l` at least ties it, so `l` is not the unique
winner. -/
def misclassified (m : ℕ) (l : Fin m) : Set (Vec ℝ m) := {y | ∃ j, j ≠ l ∧ y l ≤ y j}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
