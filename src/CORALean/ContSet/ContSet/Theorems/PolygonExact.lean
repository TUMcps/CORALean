import CORALean.ContSet.ContSet.Operations.Polygon
import CORALean.ContSet.Polygon.Real.Theorems.ConstructOfPieces

/-!
# `polygon(S)` is `S`

The polygon built from the vertices of a set with exact vertices denotes the set: an equality,
because the vertex hull is the set (`ExactVertices.vertices_exact`).

Source: [1].

## References

* [1] `contSet/@contSet/polygon.m`, CORA (Sep. 2025).
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Real

variable {S : Type} [ContSet S (Vec ℝ 2)] [ExactVertices S (Vec ℝ 2)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ContSet.construct_polygon (s : S) : construct (ContSet.polygon s) = construct s := by
  unfold ContSet.polygon
  rw [Polygon.construct_ofPieces]
  simpa using ExactVertices.vertices_exact s

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
