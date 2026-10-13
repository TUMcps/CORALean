import CORALean.ContSet.Capsule.Float.Operations.Enclose
import CORALean.ContSet.Capsule.Float.Theorems.ConvHullOuter
import CORALean.ContSet.Capsule.Float.Theorems.MtimesOuter

/-!
# `Capsule.enclose` encloses the hull of `C` and `M Cplus`

As the exact layer: the segments between `C` and the image of `Cplus` lie in the hull of `C` and
the stored `M Cplus`, `convHull_outer` after `mtimes_outer`. Outer, and of the set the code
computes, not of the documented `M C ⊕ Cplus`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open CORALean Pointwise Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.enclose_outer (k : ℕ) (C : Capsule 𝕋 n) (M : Mat 𝕋 n m) (Cplus : Capsule 𝕋 m) :
    segments C.construct ((toRealMat M *ᵥ ·) '' Cplus.construct) ⊆
      (C.enclose k M Cplus).construct := by
  refine Set.Subset.trans ?_ (Capsule.convHull_outer k C (Capsule.mtimes k M Cplus))
  rintro _ ⟨y₁, h₁, y₂, h₂, l, hl, rfl⟩
  exact ⟨y₁, h₁, y₂, Capsule.mtimes_outer k M Cplus h₂, l, hl, rfl⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
