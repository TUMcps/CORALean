module

public import CORALean.ContSet.Zoo.Real.Operations.Basic

@[expose] public section

/-!
# `ContSet/Zoo/Real/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


-- ====================================  `Zoo.uplus_outer`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

variable {n : ℕ}

/-- `Zoo.uplus` encloses the function -/
theorem Zoo.uplus_outer {Z : Zoo n} {f : Vec ℝ n → ℝ} (h : Z.Encloses f) :
    Z.uplus.Encloses f := h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
