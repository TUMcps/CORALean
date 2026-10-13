module

public import CORALean.ContSet.Polygon.Float.Operations.Project
public import CORALean.ContSet.VPolytope.Float.Theorems.ProjectOuter

@[expose] public section

/-!
# `Polygon.project` encloses the image

Piece by piece (`VPolytope.project_outer`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.project_outer (P : Polygon 𝕋) (dims : Fin 2 → Fin 2) :
    (fun x k => x (dims k)) '' ContSet.construct P ⊆
      ContSet.construct (Polygon.project P dims) := by
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨p, hp, hy⟩ := SetUnion.mem_construct.mp hy
  exact SetUnion.mem_construct.mpr ⟨_, List.mem_map.mpr ⟨p, hp, rfl⟩,
    VPolytope.project_outer p dims ⟨y, hy, rfl⟩⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
