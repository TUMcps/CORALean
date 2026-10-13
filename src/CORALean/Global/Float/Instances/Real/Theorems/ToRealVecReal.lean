import CORALean.Global.Float.Instances.Real.Instances

/-!
# A real vector reads as itself

`toRealVec` at the ℝ model is the identity, by `rfl`: the entrywise reading `toReal_real` is.
Named because a generic statement at `𝕋 := ℝ` carries it and a rewrite has to remove it.
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

@[simp] theorem toRealVec_real (v : Vec ℝ n) : toRealVec v = v := rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
