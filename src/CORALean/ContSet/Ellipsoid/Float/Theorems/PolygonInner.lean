module

public import CORALean.ContSet.Ellipsoid.Float.Operations.Polygon
public import CORALean.ContSet.Ellipsoid.Float.Theorems.ContainsPointSound
public import CORALean.ContSet.Ellipsoid.Float.Theorems.Basic
public import CORALean.ContSet.Polygon.Float.Theorems.Basic
public import CORALean.ContSet.VPolytope.Float.Theorems.EnclosePointsExact

@[expose] public section

/-!
# `Ellipsoid.polygon` lies inside the float ellipsoid

Inner: every kept vertex is a point of the ellipsoid by `Ellipsoid.containsPoint_sound`, the
ellipsoid is convex, and the polygon is the hull of the kept vertices (`enclosePoints_exact`, the
origin error box adding nothing). Nothing is claimed of the vertices dropped.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.polygon_inner (E : Ellipsoid 𝕋 2) (U : List (Vec 𝕋 E.k)) :
    ContSet.construct (E.polygon U) ⊆ E.construct := by -- --- PROOF ---
  rw [Ellipsoid.polygon, Polygon.construct_ofPieces]
  simp only [List.mem_singleton, Set.iUnion_iUnion_eq_left]
  rw [VPolytope.enclosePoints_exact]
  refine convexHull_min ?_ E.convex_construct
  rintro _ ⟨l, rfl⟩
  -- the kept factor `kept[l]` passed the test with its own vertex
  have hmem := List.getElem_mem (l := U.filter fun u => E.containsPoint
    (fun i => addUp (E.q i) (dotUp (fun j => E.G i j) u)) u) l.isLt
  exact Ellipsoid.containsPoint_sound (List.mem_filter.mp hmem).2

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
