import CORALean.ContSet.ConPolyZono.Real.ConPolyZono

/-!
# `ConPolyZono.consCol`

Constraint column `l` as a vector, which is the generator the merge adds.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Real

/-- Constraint column `l` as a vector, which is the generator the merge adds. -/
def ConPolyZono.consCol {m s : ℕ} (A : Mat ℝ m s) (l : Fin s) : Vec ℝ m := fun i => A i l

end CORALean.Real
