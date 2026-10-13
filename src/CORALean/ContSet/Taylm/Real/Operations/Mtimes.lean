module

public import CORALean.ContSet.Taylm.Real.Operations.Sum
public import CORALean.ContSet.Taylm.Real.Operations.Smul

@[expose] public section

/-!
# `Taylm.mtimes`

CORA's `mtimes` of a numeric matrix and an array of models: row `i` is `Σⱼ M i j · T j`,
the loop CORA runs with `times` and `plus`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.mtimes {k m : ℕ} (M : Mat ℝ k m) (T : Fin m → Taylm n) : Fin k → Taylm n :=
  fun i => Taylm.sum fun j => (T j).smul (M i j)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
