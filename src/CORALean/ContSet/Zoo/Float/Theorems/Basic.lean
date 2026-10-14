module

public import CORALean.ContSet.Zoo.Float.Operations.Basic

@[expose] public section

/-!
# `ContSet/Zoo/Float/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


-- ====================================  `Zoo.uplus_outer`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

/-- The zoo itself. -/
theorem Zoo.uplus_outer {Z : Zoo 𝕋 n} {f : Vec ℝ n → ℝ} (h : Z.Encloses f) :
    Z.uplus.Encloses f := h

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
