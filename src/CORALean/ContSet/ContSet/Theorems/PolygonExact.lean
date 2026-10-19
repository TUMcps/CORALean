module

public import CORALean.ContSet.ContSet.Operations.Polygon
public import CORALean.ContSet.Polygon.Real.Theorems.Basic

@[expose] public section

/-!
# `polygon(S)` is `S`

The polygon built from the vertices of a set with exact vertices denotes the set: an equality,
because the vertex hull is the set (`ExactVertices.vertices_exact`).

Source: [1].

## Inputs
* `s` – set

## Hypotheses
* none

## Conclusion
* the polygon denotes the same set as `s`

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


-- =======================================  MAIN THEOREM  ======================================= --

theorem ContSet.construct_polygon (s : S) : construct (ContSet.polygon s) = construct s := by
  unfold ContSet.polygon
  rw [Polygon.construct_ofPieces]
  simpa using ExactVertices.vertices_exact s

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
