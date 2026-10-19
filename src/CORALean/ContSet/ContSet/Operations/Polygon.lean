module

public import CORALean.ContSet.ContSet.Definitions.ExactVertices
public import CORALean.ContSet.Polygon.Real.Operations.OfPieces

@[expose] public section

/-!
# CORA's `contSet/polygon`

`polygon(S)` for a two-dimensional set: `polygon(vertices(S))`, and `convHull_` of it where `S` is
convex. Written over the classes, as the polygon with the one convex piece `vertices s`: a
representation with `ExactVertices` gets it. The piece is the whole set, so CORA's convex hull
step has nothing left to do (`ContSet.construct_polygon`). CORA's `polyshape` boundary
(vertex order, collinear points) is not modelled, as for `Polygon.ofPieces`.

Source: [1].

## Inputs
* `s` – set

## Output
* polygon of the vertex polytope of `s`

## References

* [1] `contSet/@contSet/polygon.m`, CORA (Sep. 2025).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Real

variable {S : Type} [ContSet S (Vec ℝ 2)] [ExactVertices S (Vec ℝ 2)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `polygon(S)`: the polygon whose one convex piece is the vertex polytope of `S`. -/
def ContSet.polygon (s : S) : Polygon :=
  let V := ExactVertices.vertices s                      -- vertices(S)
  Polygon.ofPieces [V]                                   -- polygon(V)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
