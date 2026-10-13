import CORALean.ContSet.Taylm.Real.Operations.Uplus

/-!
# `Taylm.uplus` encloses the function
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.uplus_outer {T : Taylm n} {f : Vec ℝ n → ℝ} (h : T.Encloses f) :
    T.uplus.Encloses f := h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
