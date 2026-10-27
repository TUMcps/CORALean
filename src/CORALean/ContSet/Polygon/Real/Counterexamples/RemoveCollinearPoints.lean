module

public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.Data.List.Sort
public import CORALean.ContSet.Polygon.Real.Polygon
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `removeCollinearPoints` changes the polygon: the angular sort is not the boundary order

CORA's `@polygon/removeCollinearPoints.m` hands the vertices to `removeCollinearVertices2D`, which
sorts them by `atan2` about their mean and drops every vertex whose two adjacent edge vectors are
dependent (`rank(vectors(:, i:i+1), tol) < 2`, `tol = 0`). The angular order is the boundary only
for a polygon star-shaped about the mean. For the U shape
`(0,0), (3,0), (3,3), (2,3), (2,1), (1,1), (1,3), (0,3)` (mean `(3/2, 7/4)`, outside it) the result
has the notch at the bottom where the U had it at the top: both have area `7`, and `(3/2, 2)` is in
the result and not in the U. The `atan2` sort is replaced by the comparison it performs, exact over
`ℚ`; the region of a vertex list is its even-odd region, as for `polyshape` (R-PG).

## Inputs
* none

## Hypotheses
* none

## Conclusion
* `removeCollinearPoints` changes the polygon: the angular sort is not the boundary order
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   13-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- A point of the plane. -/
@[step_of Polygon.removeCollinearPoints_counterexample]
abbrev Polygon.step_Pt2 : Type := ℚ × ℚ

/-- The mean of the vertices, `mean(V, 2)`. -/
@[step_of Polygon.removeCollinearPoints_counterexample]
def Polygon.step_meanV (V : List Polygon.step_Pt2) : Polygon.step_Pt2 :=
  (((V.map Prod.fst).sum) / V.length, ((V.map Prod.snd).sum) / V.length)

/-- The sector of `atan2(y, x)` in its range `(-π, π]`: `0` for `y < 0`, `1` for `y = 0, x ≥ 0`,
`2` for `y > 0`, `3` for `y = 0, x < 0`. -/
@[step_of Polygon.removeCollinearPoints_counterexample]
def Polygon.step_sector (v : Polygon.step_Pt2) : ℕ :=
  if v.2 < 0 then 0 else if v.2 = 0 then (if 0 ≤ v.1 then 1 else 3) else 2

/-- `atan2 a ≤ atan2 b` for the vectors `a`, `b` from the mean. -/
@[step_of Polygon.removeCollinearPoints_counterexample]
def Polygon.step_angleLe (a b : Polygon.step_Pt2) : Bool :=
  let sa := Polygon.step_sector a
  let sb := Polygon.step_sector b
  let cross := a.1 * b.2 - a.2 * b.1
  if sa < sb ∨ (sa = sb ∧ 0 ≤ cross) then true else false

/-- `[~, angleIdx] = sort(angle); V = V(:, angleIdx)`, by insertion sort (the keys are distinct
on the example, so every sort agrees). -/
@[step_of Polygon.removeCollinearPoints_counterexample]
def Polygon.step_sortByAngle (V : List Polygon.step_Pt2) : List Polygon.step_Pt2 :=
  let meanV := Polygon.step_meanV V
  V.insertionSort fun a b =>
    Polygon.step_angleLe (a.1 - meanV.1, a.2 - meanV.2) (b.1 - meanV.1, b.2 - meanV.2) = true

/-- `rank(vectors(:, i:i+1), 0) < 2`: the edge vectors into and out of vertex `i` are dependent.
-/
@[step_of Polygon.removeCollinearPoints_counterexample]
def Polygon.step_collinearAt (V : List Polygon.step_Pt2) (i : ℕ) : Bool :=
  let n := V.length
  let prev := V.getD ((i + n - 1) % n) (0, 0)
  let cur := V.getD i (0, 0)
  let next := V.getD ((i + 1) % n) (0, 0)
  let vi := (cur.1 - prev.1, cur.2 - prev.2)
  let vj := (next.1 - cur.1, next.2 - cur.2)
  if vi.1 * vj.2 - vi.2 * vj.1 = 0 then true else false

/-- `removeCollinearVertices2D` at `tol = 0`: sort by angle, then drop the collinear vertices.
(The early exit once two vertices remain is not reached on the example.) -/
@[step_of Polygon.removeCollinearPoints_counterexample]
def Polygon.step_removeCollinearVertices2D (V : List Polygon.step_Pt2) : List Polygon.step_Pt2 :=
  let sorted := Polygon.step_sortByAngle V
  (sorted.zipIdx.filter fun vi => !Polygon.step_collinearAt sorted vi.2).map Prod.fst

/-- Whether the rightward ray from `p` crosses the edge `a → b`. -/
@[step_of Polygon.removeCollinearPoints_counterexample]
def Polygon.step_crosses (p a b : Polygon.step_Pt2) : Bool :=
  if (a.2 > p.2 ↔ ¬ b.2 > p.2) ∧ p.1 < a.1 + (p.2 - a.2) * (b.1 - a.1) / (b.2 - a.2)
  then true else false

/-- `p` lies in the even-odd region of the closed polyline `V`. -/
@[step_of Polygon.removeCollinearPoints_counterexample]
def Polygon.step_evenOdd (V : List Polygon.step_Pt2) (p : Polygon.step_Pt2) : Bool :=
  let edges := V.zip (V.rotate 1)
  (edges.filter fun e => Polygon.step_crosses p e.1 e.2).length % 2 == 1

/-- The shoelace area of the closed polyline `V`. -/
@[step_of Polygon.removeCollinearPoints_counterexample]
def Polygon.step_shoelace (V : List Polygon.step_Pt2) : ℚ :=
  |(((V.zip (V.rotate 1)).map fun e => e.1.1 * e.2.2 - e.2.1 * e.1.2).sum)| / 2

/-- The U shape. -/
@[step_of Polygon.removeCollinearPoints_counterexample]
def Polygon.step_uShape : List Polygon.step_Pt2 :=
  [(0,0), (3,0), (3,3), (2,3), (2,1), (1,1), (1,3), (0,3)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The sort of the U is `(0,0), (1,1), (2,1), (3,0), (3,3), (2,3), (1,3), (0,3)`; the result is
`(0,0), (1,1), (2,1), (3,0), (3,3), (0,3)`, both have area `7`, `(3/2, 2)` is in the result only. -/
theorem Polygon.removeCollinearPoints_counterexample : -- --- CONCL ---
    let U := Polygon.step_uShape
    let R := Polygon.step_removeCollinearVertices2D U
    Polygon.step_sortByAngle U = [(0,0), (1,1), (2,1), (3,0), (3,3), (2,3), (1,3), (0,3)] ∧
      R = [(0,0), (1,1), (2,1), (3,0), (3,3), (0,3)] ∧
      Polygon.step_shoelace U = 7 ∧ Polygon.step_shoelace R = 7 ∧
      Polygon.step_evenOdd R (3/2, 2) = true ∧
      Polygon.step_evenOdd U (3/2, 2) = false := by -- --- PROOF ---
  intro U R
  simp only [U, R]
  -- the sort, by the exported equations of `insertionSort` and `orderedInsert`
  have hs : Polygon.step_sortByAngle Polygon.step_uShape =
      [(0,0), (1,1), (2,1), (3,0), (3,3), (2,3), (1,3), (0,3)] := by
    simp [Polygon.step_sortByAngle, Polygon.step_uShape, Polygon.step_meanV,
      List.insertionSort_nil, List.insertionSort_cons, List.orderedInsert_nil,
      List.orderedInsert_cons, Polygon.step_angleLe, Polygon.step_sector]
    norm_num
  -- then the collinear vertices dropped from it
  have hr : Polygon.step_removeCollinearVertices2D Polygon.step_uShape =
      [(0,0), (1,1), (2,1), (3,0), (3,3), (0,3)] := by
    simp [Polygon.step_removeCollinearVertices2D, hs, Polygon.step_collinearAt, List.zipIdx]
    norm_num
  -- the areas and the point test, by evaluating the sums over the rationals
  refine ⟨hs, hr, ?_, ?_, ?_, ?_⟩
  · simp [Polygon.step_shoelace, Polygon.step_uShape, List.rotate]
    norm_num
  · simp [Polygon.step_shoelace, hr, List.rotate]
    norm_num
  · simp [Polygon.step_evenOdd, hr, Polygon.step_crosses, List.rotate]
    norm_num
  · simp [Polygon.step_evenOdd, Polygon.step_uShape, Polygon.step_crosses, List.rotate]
    norm_num

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
