import CORALean.Global.Float.Instances.Real.Instances

/-!
# A real matrix reads as itself

`toRealMat` at the ℝ model is the identity, by `rfl`, as `toRealVec_real` is for a vector.
A layer written once over the scalar states its map with `toRealMat W`; at `𝕋 := ℝ` this is
what turns that back into `W`.
-/

-- Authors:       Tobias Ladner
-- Written:       23-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

@[simp] theorem toRealMat_real (M : Mat ℝ m n) : toRealMat M = M := rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
