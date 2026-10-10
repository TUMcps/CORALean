import CORALean.ContSet.ContSet.ContSet
import CORALean.ContSet.VPolytope.Real.VPolytope

/-!
# Representations with exact vertices

A representation that denotes a polytope and can list its vertices: `vertices s` is a vertex
polytope denoting exactly what `s` does. What CORA's `vertices_` returns for a convex polytopal
set, and what `contSet/polygon` builds its region from. It is a guarantee, so the class holds
only where the vertex hull is the whole set: a box or a zonotope, a vertex polytope itself; not a
polytope given by halfspaces, which may be unbounded, and not a representation whose vertices are
sampled (an ellipsoid, a capsule).
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Real


-- ========================================  MAIN TYPE  ========================================= --

/-- The vertices of `s`, as a vertex polytope that denotes exactly `s`. -/
class ExactVertices (S : Type) (α : outParam Type) [AddCommGroup α] [Module ℝ α]
    [ContSet S α] where
  vertices : S → VPolytope α
  vertices_exact (s : S) : (vertices s).construct = construct s

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
