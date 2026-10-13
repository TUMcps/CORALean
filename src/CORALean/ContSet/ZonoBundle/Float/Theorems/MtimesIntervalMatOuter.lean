import CORALean.ContSet.ZonoBundle.Float.Operations.MtimesIntervalMat
import CORALean.ContSet.Zonotope.Float.Theorems.MtimesIntervalMatOuter

/-!
# `ZonoBundle.mtimesIntervalMat` over-approximates every image

Sound because `A (⋂ᵢ Zᵢ) ⊆ ⋂ᵢ A Zᵢ` for each `A` of the interval matrix: a point in every
member maps into every image, and `Zonotope.mtimesIntervalMat_outer` encloses that image in
the member of the mapped bundle it came from.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.mtimesIntervalMat_outer (IM : Interval (Mat 𝕋 m n)) (zB : ZonoBundle (Vec 𝕋 n)) :
    (⋃ A ∈ IM.construct, (A *ᵥ ·) '' zB.construct) ⊆
      (zB.mtimesIntervalMat IM).construct := by -- --- PROOF ---
  intro y hy
  simp only [Set.mem_iUnion, Set.mem_image, exists_prop] at hy
  obtain ⟨A, hA, a, ha, rfl⟩ := hy
  simp only [ZonoBundle.construct, Set.mem_iInter] at ha ⊢
  intro i
  exact Zonotope.mtimesIntervalMat_outer IM (zB.Z i)
    (Set.mem_biUnion hA (Set.mem_image_of_mem _ (ha i)))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
