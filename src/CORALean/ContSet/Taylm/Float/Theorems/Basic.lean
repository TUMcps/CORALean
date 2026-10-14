module

public import CORALean.ContSet.Taylm.Float.Operations.Basic
public import CORALean.ContSet.Taylm.Float.Theorems.PlusOuter
public import CORALean.ContSet.Taylm.Float.Theorems.SmulOuter
public import CORALean.ContSet.Taylm.Float.Theorems.SumOuter
public import CORALean.ContSet.Taylm.Float.Theorems.UminusOuter

@[expose] public section

/-!
# `ContSet/Taylm/Float/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


-- ===================================  `Taylm.const_outer`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

/-- `Taylm.const` encloses the constant -/
theorem Taylm.const_outer (c : 𝕋) (N : ℕ) :
    (Taylm.const n c N).Encloses fun _ => toReal c := by
  intro t _
  simp [Taylm.const, Taylm.nominal, Real.Taylm.poly, Real.Taylm.monomial_zero, toReal_zero]

end CORALean.Float


-- ===================================  `Taylm.minus_outer`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

/-- `Taylm.minus` encloses the difference -/
theorem Taylm.minus_outer {T₁ T₂ : Taylm 𝕋 n} {f g : Vec ℝ n → ℝ} (h₁ : T₁.Encloses f)
    (h₂ : T₂.Encloses g) : (T₁.minus T₂).Encloses fun t => f t - g t := by
  show (T₁.plus T₂.uminus).Encloses _
  simpa only [sub_eq_add_neg] using Taylm.plus_outer h₁ (Taylm.uminus_outer h₂)

end CORALean.Float


-- ===================================  `Taylm.mtimes_outer`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

/-- `Taylm.mtimes` encloses the matrix image -/
theorem Taylm.mtimes_outer {k m : ℕ} (M : Mat 𝕋 k m) {T : Fin m → Taylm 𝕋 n}
    {f : Fin m → Vec ℝ n → ℝ} (h : ∀ j, (T j).Encloses (f j)) (i : Fin k) :
    (Taylm.mtimes M T i).Encloses fun t => ∑ j, toReal (M i j) * f j t :=
  Taylm.sum_outer fun j => Taylm.smul_outer ⟨le_refl _, le_refl _⟩ (h j)

end CORALean.Float


-- ===================================  `Taylm.trace_outer`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

/-- `Taylm.trace` encloses the trace -/
theorem Taylm.trace_outer {k : ℕ} {A : Fin k → Fin k → Taylm 𝕋 n}
    {f : Fin k → Fin k → Vec ℝ n → ℝ} (h : ∀ i j, (A i j).Encloses (f i j)) :
    (Taylm.trace A).Encloses fun t => ∑ i, f i i t :=
  Taylm.sum_outer fun i => h i i

end CORALean.Float


-- ===================================  `Taylm.uplus_outer`  ==================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

/-- `Taylm.uplus` encloses the function, over a floating-point scalar -/
theorem Taylm.uplus_outer {T : Taylm 𝕋 n} {f : Vec ℝ n → ℝ} (h : T.Encloses f) :
    T.uplus.Encloses f := h

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
