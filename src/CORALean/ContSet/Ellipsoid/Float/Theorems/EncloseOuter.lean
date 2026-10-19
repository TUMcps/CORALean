module

public import CORALean.ContSet.Ellipsoid.Float.Operations.Enclose
public import CORALean.ContSet.Ellipsoid.Float.Theorems.Basic
public import CORALean.ContSet.Ellipsoid.Float.Theorems.MtimesOuter

@[expose] public section

/-!
# `Ellipsoid.enclose` contains the segments

Each segment runs from a point of `E` to the image of a point of `Eplus`, which lies in the
float `M * Eplus` (`Ellipsoid.mtimes_outer`); both ends are in the hull by its contract, and the
float hull is convex (`Ellipsoid.convex_construct`), so the segment is too. Outer, as over ℝ.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open scoped Matrix
open SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.enclose_outer (orOA : Ellipsoid 𝕋 n → Ellipsoid 𝕋 n → Ellipsoid 𝕋 n)
    (hor : ∀ E₁ E₂, E₁.construct ∪ E₂.construct ⊆ (orOA E₁ E₂).construct)
    (E : Ellipsoid 𝕋 n) (M : Mat 𝕋 n m) (Eplus : Ellipsoid 𝕋 m) : -- --- CONCL ---
    Set.linComb E.construct ((toRealMat M *ᵥ ·) '' Eplus.construct) ⊆
      (Ellipsoid.enclose orOA E M Eplus).construct := by -- --- PROOF ---
  rintro _ ⟨y₁, h₁, y₂, h₂, l, ⟨hl0, hl1⟩, rfl⟩
  -- the image end lies in the float image, and both ends in the hull
  have h₂' := Ellipsoid.mtimes_outer M Eplus h₂
  exact (Ellipsoid.convex_construct _) (hor _ _ (Or.inl h₁)) (hor _ _ (Or.inr h₂')) hl0
    (by linarith) (by ring)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
