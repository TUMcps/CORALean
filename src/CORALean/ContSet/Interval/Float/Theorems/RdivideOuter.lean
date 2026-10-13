module

public import CORALean.ContSet.Interval.Float.Operations.Rdivide
public import CORALean.ContSet.Interval.Float.Theorems.RecipOuter
public import CORALean.ContSet.Interval.Float.Theorems.TimesOuter

@[expose] public section

/-!
# `Interval.rdivide` over-approximates the entrywise quotients, over a floating-point scalar

A quotient is the numerator point times the reciprocal of the denominator point:
`recip_outer` puts the reciprocal in the reciprocal box and `times_outer` the product in the
product box.
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

theorem Interval.rdivide_outer (I J : Interval (Vec 𝕋 n))
    (hJ : ∀ i, ltStrict zero (J.inf i) = true ∨ ltStrict (J.sup i) zero = true) :
    Set.image2 (fun x y i => x i / y i) I.construct J.construct
      ⊆ (I.rdivide J).construct := by
  rintro _ ⟨x, hx, y, hy, rfl⟩
  exact Interval.times_outer I J.recip
    ⟨x, hx, fun i => (y i)⁻¹, Interval.recip_outer J hJ ⟨y, hy, rfl⟩, funext fun i => by
      simp [div_eq_mul_inv]⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
