module

public import CORALean.ContSet.Taylm.Float.Operations.Rdivide
public import CORALean.ContSet.Taylm.Float.Theorems.InvOuter
public import CORALean.ContSet.Taylm.Float.Theorems.TimesOuter

@[expose] public section

/-!
# `Taylm.rdivide` encloses `f / g`, over a floating-point scalar

`T₁ · (1/T₂)`: `times_outer` at the enclosure of `1/g` that `inv_outer` gives, under the same
condition on the denominator's hull.

## Inputs
* `T₁` – numerator model
* `T₂` – denominator model
* `f` – numerator function
* `g` – denominator function

## Hypotheses
* `h₁` – the numerator encloses its function
* `h₂` – the denominator encloses its function
* `hm` – the denominator's range stays away from zero

## Conclusion
* the quotient model encloses the quotient of the functions
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.rdivide_outer {T₁ T₂ : Taylm 𝕋 n} {f g : Vec ℝ n → ℝ} (h₁ : T₁.Encloses f)
    (h₂ : T₂.Encloses g)
    (hm : 0 < toReal (maximum (minimum T₂.constCoef T₂.bounds.inf)
      (neg (maximum T₂.constCoef T₂.bounds.sup)))) : -- --- CONCL ---
    (T₁.rdivide T₂).Encloses fun t => f t / g t := by -- --- PROOF ---
  simpa [Taylm.rdivide, div_eq_mul_inv] using Taylm.times_outer h₁ (Taylm.inv_outer h₂ hm)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
