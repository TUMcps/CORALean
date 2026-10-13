module

public import CORALean.ContSet.SpectraShadow.Float.Theorems.ConvHullOuter
public import CORALean.ContSet.ContSet.Theorems.SegmentsEqConvexJoin
public import Mathlib.Analysis.Convex.Join

@[expose] public section

/-!
# The segments between two float shadows are inside their convex hull's enclosure

`segments` is Mathlib's convex join, which lies in the hull of the union, and `convHull_outer`
puts the hull inside the result. That is the guarantee `LinComb` asks of `convHull_`, and so of
`enclose` and `or`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.segments_subset_convHull (S₁ S₂ : SpectraShadow 𝕋 (Vec 𝕋 n)) :
    CORALean.segments S₁.construct S₂.construct ⊆ (S₁.convHull_ S₂).construct := by
  rw [CORALean.segments_eq_convexJoin]
  exact (convexJoin_subset_convexHull _ _).trans (SpectraShadow.convHull_outer S₁ S₂)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
