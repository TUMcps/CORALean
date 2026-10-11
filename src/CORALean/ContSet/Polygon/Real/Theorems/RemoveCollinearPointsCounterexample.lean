import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Data.List.Sort
import CORALean.ContSet.Polygon.Real.Polygon

/-!
# `removeCollinearPoints` changes the polygon: the angular sort is not the boundary order

CORA's `@polygon/removeCollinearPoints.m` hands the vertices to `removeCollinearVertices2D`,
which sorts them by `atan2` about their mean and then drops every vertex whose two adjacent edge
vectors are dependent (`rank(vectors(:, i:i+1), tol) < 2`, with `tol = 0`). The angular order is
the boundary only for a polygon star-shaped about the mean.

For the U shape `(0,0), (3,0), (3,3), (2,3), (2,1), (1,1), (1,3), (0,3)` (mean `(3/2, 7/4)`,
outside the polygon) the sorted order is `(0,0), (1,1), (2,1), (3,0), (3,3), (2,3), (1,3), (0,3)`,
the two collinear top vertices `(2,3), (1,3)` go, and the polygon
`(0,0), (1,1), (2,1), (3,0), (3,3), (0,3)` has the notch at the bottom where the U had it at the
top. Both have area `7`, and `(3/2, 2)` is in the result and not in the U.

Two stand-ins, exact over `ℚ`. The `atan2` sort is the comparison it performs: `atan2` increases
across the sectors `y < 0`, `y = 0 ∧ x ≥ 0`, `y > 0`, `y = 0 ∧ x < 0` about the mean, and within a
sector (a span of at most `π`) `a` precedes `b` iff `cross a b ≥ 0`; `Complex.arg` is not
evaluated. The region of a vertex list is its even-odd (crossing number) region, as for MATLAB's
`polyshape` of a simple polygon; a `Polygon` of convex pieces has no boundary reading (R-PG).
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A point of the plane. -/
abbrev Polygon.aux_Pt2 : Type := ℚ × ℚ

/-- The mean of the vertices, `mean(V, 2)`. -/
def Polygon.aux_meanV (V : List Polygon.aux_Pt2) : Polygon.aux_Pt2 :=
  (((V.map Prod.fst).sum) / V.length, ((V.map Prod.snd).sum) / V.length)

/-- The sector of `atan2(y, x)` in its range `(-π, π]`: `0` for `y < 0`, `1` for `y = 0, x ≥ 0`,
`2` for `y > 0`, `3` for `y = 0, x < 0`. -/
def Polygon.aux_sector (v : Polygon.aux_Pt2) : ℕ :=
  if v.2 < 0 then 0 else if v.2 = 0 then (if 0 ≤ v.1 then 1 else 3) else 2

/-- `atan2 a ≤ atan2 b` for the vectors `a`, `b` from the mean. -/
def Polygon.aux_angleLe (a b : Polygon.aux_Pt2) : Bool :=
  let sa := Polygon.aux_sector a
  let sb := Polygon.aux_sector b
  let cross := a.1 * b.2 - a.2 * b.1
  if sa < sb ∨ (sa = sb ∧ 0 ≤ cross) then true else false

/-- `[~, angleIdx] = sort(angle); V = V(:, angleIdx)`, by insertion sort (the keys are distinct
on the example, so every sort agrees). -/
def Polygon.aux_sortByAngle (V : List Polygon.aux_Pt2) : List Polygon.aux_Pt2 :=
  let meanV := Polygon.aux_meanV V
  V.insertionSort fun a b =>
    Polygon.aux_angleLe (a.1 - meanV.1, a.2 - meanV.2) (b.1 - meanV.1, b.2 - meanV.2) = true

/-- `rank(vectors(:, i:i+1), 0) < 2`: the edge vectors into and out of vertex `i` are dependent.
-/
def Polygon.aux_collinearAt (V : List Polygon.aux_Pt2) (i : ℕ) : Bool :=
  let n := V.length
  let prev := V.getD ((i + n - 1) % n) (0, 0)
  let cur := V.getD i (0, 0)
  let next := V.getD ((i + 1) % n) (0, 0)
  let vi := (cur.1 - prev.1, cur.2 - prev.2)
  let vj := (next.1 - cur.1, next.2 - cur.2)
  if vi.1 * vj.2 - vi.2 * vj.1 = 0 then true else false

/-- `removeCollinearVertices2D` at `tol = 0`: sort by angle, then drop the collinear vertices.
(The early exit once two vertices remain is not reached on the example.) -/
def Polygon.aux_removeCollinearVertices2D (V : List Polygon.aux_Pt2) : List Polygon.aux_Pt2 :=
  let sorted := Polygon.aux_sortByAngle V
  (sorted.zipIdx.filter fun vi => !Polygon.aux_collinearAt sorted vi.2).map Prod.fst


/-- Whether the rightward ray from `p` crosses the edge `a → b`. -/
def Polygon.aux_crosses (p a b : Polygon.aux_Pt2) : Bool :=
  if (a.2 > p.2 ↔ ¬ b.2 > p.2) ∧ p.1 < a.1 + (p.2 - a.2) * (b.1 - a.1) / (b.2 - a.2)
  then true else false

/-- `p` lies in the even-odd region of the closed polyline `V`. -/
def Polygon.aux_evenOdd (V : List Polygon.aux_Pt2) (p : Polygon.aux_Pt2) : Bool :=
  let edges := V.zip (V.rotate 1)
  (edges.filter fun e => Polygon.aux_crosses p e.1 e.2).length % 2 == 1

/-- The shoelace area of the closed polyline `V`. -/
def Polygon.aux_shoelace (V : List Polygon.aux_Pt2) : ℚ :=
  |(((V.zip (V.rotate 1)).map fun e => e.1.1 * e.2.2 - e.2.1 * e.1.2).sum)| / 2
/-- The U shape. -/
def Polygon.aux_uShape : List Polygon.aux_Pt2 :=
  [(0,0), (3,0), (3,3), (2,3), (2,1), (1,1), (1,3), (0,3)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The sort of the U is `(0,0), (1,1), (2,1), (3,0), (3,3), (2,3), (1,3), (0,3)`; the result is
`(0,0), (1,1), (2,1), (3,0), (3,3), (0,3)`, both have area `7`, `(3/2, 2)` is in the result only. -/
theorem Polygon.removeCollinearPoints_counterexample :
    Polygon.aux_sortByAngle Polygon.aux_uShape =
        [(0,0), (1,1), (2,1), (3,0), (3,3), (2,3), (1,3), (0,3)] ∧
      Polygon.aux_removeCollinearVertices2D Polygon.aux_uShape =
        [(0,0), (1,1), (2,1), (3,0), (3,3), (0,3)] ∧
      Polygon.aux_shoelace Polygon.aux_uShape = 7 ∧
      Polygon.aux_shoelace (Polygon.aux_removeCollinearVertices2D Polygon.aux_uShape) = 7 ∧
      Polygon.aux_evenOdd (Polygon.aux_removeCollinearVertices2D Polygon.aux_uShape) (3/2, 2)
        = true ∧
      Polygon.aux_evenOdd Polygon.aux_uShape (3/2, 2) = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> with_unfolding_all rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
