module

public import CORALean.ContSet.Zonotope.Real.Operations.Vertices
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeVPolytopeExact
public import CORALean.ContSet.VPolytope.Real.Theorems.ConvexHull

@[expose] public section

/-!
# A zonotope is the convex hull of its vertices

`vPolytope_exact` says the sign corners denote the zonotope, and a vertex polytope is the hull of
its vertex list (`construct_eq_convexHull`); the list of `vertices` is that range, as `signEquiv`
reaches every choice of signs.

## Inputs
* `Z` – zonotope

## Hypotheses
* none

## Conclusion
* the hull of the vertices is `Z`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The hull of the vertices is the zonotope: nothing is added and nothing lost. -/
theorem Zonotope.convexHull_vertices (Z : Zonotope α) :
    convexHull ℝ (Z.vertices : Set α) = Z.construct := by -- --- PROOF ---
  rw [← Zonotope.vPolytope_exact, VPolytope.construct_eq_convexHull]
  congr 1
  ext x
  simp only [Zonotope.vertices, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range,
    Zonotope.vPolytope]
  exact ⟨fun ⟨σ, hσ⟩ => ⟨(signEquiv Z.h).symm σ, by simpa using hσ⟩, fun ⟨l, hl⟩ => ⟨_, hl⟩⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
