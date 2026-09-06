import CORALean.Global.Tensor

/-!
# The set a classifier must avoid

The unsafe set a classification requirement is checked against: some label
other than the target at least ties it, so the target is not the unique
winner. Shared by `Robustness` and the sufficient-explanation theorems, which
state the same requirement over an abstract network's output.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Some label other than `l` at least ties it, so `l` is not the unique
winner. -/
def misclassified (m : ℕ) (l : Fin m) : Set (Vec ℝ m) := {y | ∃ j, j ≠ l ∧ y l ≤ y j}

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
