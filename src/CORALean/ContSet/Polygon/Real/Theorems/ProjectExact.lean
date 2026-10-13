module

public import CORALean.ContSet.Polygon.Real.Operations.Project
public import CORALean.ContSet.VPolytope.Real.Instances
public import CORALean.ContSet.VPolytope.Real.Theorems.ProjectExact

@[expose] public section

/-!
# `Polygon.project` is the image

Exactly, piece by piece (`VPolytope.project_exact`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.project_exact (P : Polygon) (dims : Fin 2 → Fin 2) :
    (fun x k => x (dims k)) '' ContSet.construct P =
      ContSet.construct (Polygon.project P dims) := by -- --- PROOF ---
  ext x
  simp only [Set.mem_image, SetUnion.mem_construct, Polygon.project, List.mem_map]
  constructor
  · rintro ⟨y, ⟨p, hp, hy⟩, rfl⟩
    refine ⟨_, ⟨p, hp, rfl⟩, ?_⟩
    rw [show ContSet.construct (VPolytope.project p dims) =
      VPolytope.construct (VPolytope.project p dims) from rfl, ← VPolytope.project_exact]
    exact ⟨y, hy, rfl⟩
  · rintro ⟨_, ⟨p, hp, rfl⟩, hx⟩
    rw [show ContSet.construct (VPolytope.project p dims) =
      VPolytope.construct (VPolytope.project p dims) from rfl, ← VPolytope.project_exact] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨y, ⟨p, hp, hy⟩, rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
