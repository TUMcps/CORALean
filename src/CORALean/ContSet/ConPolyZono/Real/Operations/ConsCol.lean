module

public import CORALean.ContSet.ConPolyZono.Real.ConPolyZono

@[expose] public section

/-!
# `ConPolyZono.consCol`

Constraint column `l` as a vector, which is the generator the merge adds.
-/

-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Constraint column `l` as a vector, which is the generator the merge adds. -/
def ConPolyZono.consCol {m s : ℕ} (A : Mat ℝ m s) (l : Fin s) : Vec ℝ m := fun i => A i l

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
