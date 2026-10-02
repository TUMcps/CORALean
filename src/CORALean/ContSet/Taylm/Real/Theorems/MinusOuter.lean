import CORALean.ContSet.Taylm.Real.Operations.Minus
import CORALean.ContSet.Taylm.Real.Theorems.PlusOuter
import CORALean.ContSet.Taylm.Real.Theorems.UminusOuter

/-!
# `Taylm.minus` encloses the difference
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.minus_outer {T₁ T₂ : Taylm n} {f g : Vec ℝ n → ℝ} (h₁ : T₁.Encloses f)
    (h₂ : T₂.Encloses g) : (T₁.minus T₂).Encloses fun t => f t - g t := by
  show (T₁.plus T₂.uminus).Encloses _
  simpa only [sub_eq_add_neg] using Taylm.plus_outer h₁ (Taylm.uminus_outer h₂)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
