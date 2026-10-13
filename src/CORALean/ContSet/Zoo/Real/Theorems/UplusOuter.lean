import CORALean.ContSet.Zoo.Real.Operations.Uplus

/-!
# `Zoo.uplus` encloses the function
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zoo.uplus_outer {Z : Zoo n} {f : Vec ℝ n → ℝ} (h : Z.Encloses f) :
    Z.uplus.Encloses f := h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
