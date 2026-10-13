import CORALean.ContSet.SpectraShadow.Float.Theorems.ConvHullOuter
import CORALean.ContSet.SpectraShadow.Float.Operations.Or

/-!
# `SpectraShadow.or` encloses the convex hull of the union, over a floating-point scalar

`or` is `convHull_`, so `convHull_outer` is its guarantee: an enclosure.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.or_outer (S₁ S₂ : SpectraShadow 𝕋 (Vec 𝕋 n)) :
    convexHull ℝ (S₁.construct ∪ S₂.construct) ⊆ (S₁.or S₂).construct :=
  SpectraShadow.convHull_outer S₁ S₂

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
