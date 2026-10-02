import CORALean.ContSet.Polygon.Float.Operations.Mtimes

/-!
# `Polygon.mtimes` encloses the image

Piece by piece (`VPolytope.mtimes_outer`).
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

open Matrix in
theorem Polygon.mtimes_outer (M : Mat 𝕋 2 2) (P : Polygon 𝕋) :
    (toRealMat M *ᵥ ·) '' ContSet.construct P ⊆
      ContSet.construct (Polygon.mtimes M P) := by -- --- PROOF ---
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨p, hp, hy⟩ := SetUnion.mem_construct.mp hy
  refine SetUnion.mem_construct.mpr ⟨_, List.mem_map.mpr ⟨p, hp, rfl⟩, ?_⟩
  have := VPolytope.mtimes_outer M p ⟨y, hy, rfl⟩
  rwa [← VPolytope.materialise_eq (VPolytope.mtimes M p)] at this

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
