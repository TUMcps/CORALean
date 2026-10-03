import CORALean.ContSet.Taylm.Float.Operations.Rdivide
import CORALean.ContSet.Taylm.Float.Theorems.InvOuter
import CORALean.ContSet.Taylm.Float.Theorems.TimesOuter

/-!
# `Taylm.rdivide` encloses `f / g`, over a floating-point scalar

`T₁ · (1/T₂)`: `times_outer` at the enclosure of `1/g` that `inv_outer` gives, under the same
condition on the denominator's hull.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.rdivide_outer {T₁ T₂ : Taylm 𝕋 n} {f g : Vec ℝ n → ℝ} (h₁ : T₁.Encloses f)
    (h₂ : T₂.Encloses g)
    (hm : 0 < toReal (maximum (minimum T₂.constCoef T₂.bounds.1)
      (neg (maximum T₂.constCoef T₂.bounds.2)))) :
    (T₁.rdivide T₂).Encloses fun t => f t / g t := by
  simpa [Taylm.rdivide, div_eq_mul_inv] using Taylm.times_outer h₁ (Taylm.inv_outer h₂ hm)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
