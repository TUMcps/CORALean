module

public import CORALean.ContSet.Taylm.Real.Taylm

@[expose] public section

/-!
# `Taylm.polyOf_nil`

What every operation's proof reads its polynomial through.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

@[simp] theorem Taylm.polyOf_nil (t : Vec ℝ n) : Taylm.polyOf [] t = 0 := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
