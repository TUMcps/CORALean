import CORALean.ContSet.Polygon.Real.Operations.Mtimes
import CORALean.ContSet.VPolytope.Real.Instances

/-!
# `Polygon.mtimes` is the image

Exactly: the image of a union is the union of the images, and each piece's image is exact.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

open Matrix in
theorem Polygon.mtimes_exact (M : Mat ℝ 2 2) (P : Polygon) :
    (M *ᵥ ·) '' ContSet.construct P = ContSet.construct (Polygon.mtimes M P) := by -- --- PROOF ---
  ext x
  simp only [Set.mem_image, SetUnion.mem_construct, Polygon.mtimes, List.mem_map]
  constructor
  · rintro ⟨y, ⟨p, hp, hy⟩, rfl⟩
    refine ⟨_, ⟨p, hp, rfl⟩, ?_⟩
    rw [show ContSet.construct (VPolytope.mtimes M p) = VPolytope.construct (VPolytope.mtimes M p)
      from rfl, ← VPolytope.mtimes_exact]
    exact ⟨y, hy, rfl⟩
  · rintro ⟨_, ⟨p, hp, rfl⟩, hx⟩
    rw [show ContSet.construct (VPolytope.mtimes M p) = VPolytope.construct (VPolytope.mtimes M p)
      from rfl, ← VPolytope.mtimes_exact] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨y, ⟨p, hp, hy⟩, rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
