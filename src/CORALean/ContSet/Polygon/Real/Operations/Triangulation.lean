import CORALean.ContSet.Polygon.Real.Polygon

/-!
# `Polygon.triangulation`

CORA's `polygon/triangulation` triangulates the `polyshape` boundary and returns the triangles as
a list of polygons. A polygon here is already a union of convex pieces, so the triangles are
those of the pieces: for every piece and every triple `(a, b, c)` of its vertices, the triangle
they span. This is a cover by triangles whose union is the region (`Polygon.triangulation_exact`),
not CORA's partition: the triangles overlap and their number is cubic in the vertex count. The
triangulation of the boundary (R-PG) is not modelled. It is the cover `linComb` and `quadMap`
need, which take unions over the triangles.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The vertex triangles of every piece. -/
def Polygon.triangulation (P : Polygon) : Polygon :=
  ⟨P.sets.flatMap fun p => (List.finRange p.k).flatMap fun a => (List.finRange p.k).flatMap
    fun b => (List.finRange p.k).map fun c => ⟨3, ![p.V a, p.V b, p.V c]⟩⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
