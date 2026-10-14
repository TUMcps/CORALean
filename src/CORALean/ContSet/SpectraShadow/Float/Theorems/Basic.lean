module

public import CORALean.ContSet.SpectraShadow.Float.Operations.Or
public import CORALean.ContSet.SpectraShadow.Float.SpectraShadow
public import CORALean.ContSet.SpectraShadow.Float.Theorems.ConvHullOuter

@[expose] public section

/-!
# `ContSet/SpectraShadow/Float/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

section

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ================================  `SpectraShadow.nominal_c`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---

/-- The nominal shadow's fields, so proofs can see through the instance. -/
theorem SpectraShadow.nominal_c [SoundFloatArithmetic 𝕋] (S : SpectraShadow 𝕋 (Vec 𝕋 n)) :
    (InflatedContSet.nominal S).c = toRealVec S.c := rfl


-- ================================  `SpectraShadow.nominal_G`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---

/-- The nominal SpectraShadow's field `G`, so proofs can see through the instance. -/
theorem SpectraShadow.nominal_G [SoundFloatArithmetic 𝕋] (S : SpectraShadow 𝕋 (Vec 𝕋 n)) :
    (InflatedContSet.nominal S).G = fun j i => toReal (S.G j i) := rfl

end


section

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =================================  `SpectraShadow.or_outer`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `or` is `convHull_`, so `convHull_outer` is its guarantee: an enclosure. -/
theorem SpectraShadow.or_outer (S₁ S₂ : SpectraShadow 𝕋 (Vec 𝕋 n)) :
    convexHull ℝ (S₁.construct ∪ S₂.construct) ⊆ (S₁.or S₂).construct :=
  SpectraShadow.convHull_outer S₁ S₂

end

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
