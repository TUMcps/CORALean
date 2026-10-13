module

public import CORALean.ContSet.Taylm.Float.Operations.Minus
public import CORALean.ContSet.Taylm.Float.Theorems.PlusOuter
public import CORALean.ContSet.Taylm.Float.Theorems.UminusOuter

@[expose] public section

/-!
# `Taylm.minus` encloses the difference
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.minus_outer {T₁ T₂ : Taylm 𝕋 n} {f g : Vec ℝ n → ℝ} (h₁ : T₁.Encloses f)
    (h₂ : T₂.Encloses g) : (T₁.minus T₂).Encloses fun t => f t - g t := by
  show (T₁.plus T₂.uminus).Encloses _
  simpa only [sub_eq_add_neg] using Taylm.plus_outer h₁ (Taylm.uminus_outer h₂)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
