import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Basic

/-!
# A linear functional's greatest value on a convex hull is taken at a generator

If `f ≤ m` on `S` and `f s = m` for some `s ∈ S`, then `m` is the greatest value of `f` on
`convexHull S`: the half-space `{f ≤ m}` is convex and so contains the hull. This is how the
support function of a polytope given by vertices is read off a vertex.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem isGreatest_image_convexHull {V : Type} [AddCommGroup V] [Module ℝ V] {S : Set V}
    (f : V →ₗ[ℝ] ℝ) {m : ℝ} (hmem : ∃ s ∈ S, f s = m) (hle : ∀ s ∈ S, f s ≤ m) :
    IsGreatest (f '' convexHull ℝ S) m := by -- --- PROOF ---
  refine ⟨?_, ?_⟩
  · obtain ⟨s, hs, rfl⟩ := hmem
    exact ⟨s, subset_convexHull ℝ S hs, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact convexHull_min (fun s hs => hle s hs) (convex_halfSpace_le f.isLinear m) hx

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
