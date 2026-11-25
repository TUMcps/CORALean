import CORALean.ContSet.Polygon.Float.Operations.Basic
import CORALean.ContSet.Polygon.Float.Operations.BoundDot
import CORALean.ContSet.Polygon.Float.Operations.ContainsPoint
import CORALean.ContSet.Polygon.Float.Operations.IsConvex
import CORALean.ContSet.Polygon.Float.Operations.IsDisjoint
import CORALean.ContSet.Polygon.Float.Operations.IsFullDim
import CORALean.ContSet.Polygon.Float.Operations.IsequalPieces
import CORALean.ContSet.Polygon.Float.Operations.Minus
import CORALean.ContSet.Polygon.Float.Operations.RepresentsaEmptySet
import CORALean.ContSet.Polygon.Float.Operations.SplitIntoConvexSets
import CORALean.ContSet.Polygon.Float.Operations.Times
import CORALean.ContSet.Polygon.Float.Operations.Vertices
import CORALean.ContSet.VPolytope.Float.Instances
import CORALean.Examples.Oracle.Ops.SetCodec

/-!
# The polygon ops: CORA's `polygon` methods

Thin adapters over the float definitions `references/coverage/contSet/polygon.md` links. A polygon
is CORALean's `Polygon`, a finite union of convex pieces, each a vertex polytope of the plane; on
the wire `{"pieces":[{"V","E"}, ...]}` (no piece: the empty polygon). Operands are `pgon`, `pgon2`;
a set result is `pgon`, a vertex polytope `P`, a box `I`, a point list `V` (one column per point),
a Boolean or a bound `value`. Indices are 0-based; a field an op does not list is refused by name.
Not served: `and`, `volume`, `triangulation`, `subtract`, `mldivide` (CORALean's are boxes or
vertex triples, not CORA's sets), `minkDiff` and `quadMap` (not yet), and the boundary methods
CORALean does not formalize (`compact`, `removeCollinearPoints`, the `polyshape` constructor).

## Inputs
* `dops` – dtype operations
* `req` – request

## Output
* response fields or an error message
-/

-- Authors:       Claude Opus 5.5
-- Written:       25-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Oracle

open CORALean CORALean.Float
open Lean (Json)

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The polygon `{"pieces":[...]}`, every piece a vertex polytope of the plane. -/
private def aux_parse (dops : DtypeOps 𝕋) (j : Json) : Except String (Polygon 𝕋) := do
  let ps ← (← arrField j "pieces").mapM (parseVPolytopeFixed dops.readExact 2)
  pure (Polygon.ofPieces ps.toList)

/-- `P` as the wire polygon. -/
private def aux_print (dops : DtypeOps 𝕋) (P : Polygon 𝕋) : Json :=
  Json.mkObj [("pieces", Json.arr (P.sets.map (printVPolytope dops.showExact)).toArray)]

private def aux_set (dops : DtypeOps 𝕋) (P : Polygon 𝕋) : String × Json :=
  ("pgon", aux_print dops P)

/-- The operand `pgon`, and `pgon2` when the op has two. -/
private def aux_one (dops : DtypeOps 𝕋) (req : Json) : Except String (Polygon 𝕋) := do
  aux_parse dops (← field req "pgon")

private def aux_two (dops : DtypeOps 𝕋) (req : Json) : Except String (Polygon 𝕋 × Polygon 𝕋) := do
  pure (← aux_parse dops (← field req "pgon"), ← aux_parse dops (← field req "pgon2"))

/-- An op of two polygons with a polygon result. -/
private def aux_binary (op : String) (dops : DtypeOps 𝕋) (req : Json)
    (f : Polygon 𝕋 → Polygon 𝕋 → Polygon 𝕋) : Resp := do
  checkFields op req ["pgon", "pgon2"]
  let (a, b) ← aux_two dops req
  pure [aux_set dops (f a b)]

/-- A matrix of `rows` rows and two columns, the `M` of `mtimes`. -/
private def aux_square (dops : DtypeOps 𝕋) (req : Json) : Except String (Mat 𝕋 2 2) := do
  let ⟨r, M⟩ ← parseMatColsFixed dops.readExact 2 (← field req "M")
  if h : r = 2 then pure (h ▸ M) else throw s!"mtimes: `M` must be 2×2, not {r}×2"


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `polygon.vertices`: the stored vertices of every piece, piece by piece, `Polygon.vertices`. -/
def handlePolygonVertices (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "vertices" req ["pgon"]
  let a := (Polygon.vertices (← aux_one dops req)).toArray
  pure [("V", printMat dops.showExact (fun (i : Fin 2) (l : Fin a.size) => a[l] i))]

/-- `polygon.supportFunc`: the largest of the pieces' upper bounds, `Polygon.boundDot`. -/
def handlePolygonSupportFunc (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "supportFunc" req ["pgon", "dir", "type"]
  checkStrOption "supportFunc" req "type" "upper"
  let P ← aux_one dops req
  if P.sets.isEmpty then throw "supportFunc: the polygon has no piece (CORA's -Inf)"
  let a ← parseVecFixed dops.readExact 2 (← field req "dir")
  valueScalar dops.showExact (P.boundDot (c := rowFunctional a) a fun _ => rfl).val

/-- `polygon.project`: the pieces read at the coordinates `dims`, two of them. -/
def handlePolygonProject (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "project" req ["pgon", "dims"]
  let P ← aux_one dops req
  let ⟨m, d⟩ ← indexArrField req "dims" 2
  if h : m = 2 then pure [aux_set dops (Polygon.project P fun i => d (Fin.cast h.symm i))]
  else throw s!"project: `dims` has {m} entries, a polygon keeps two"

/-- Every op of this file, without the `polygon.` prefix. -/
def polygonOpNames : List String :=
  [ "contains", "convHull", "empty", "interval", "isBounded", "isConvex", "isFullDim",
    "isIntersecting", "isequal", "linComb", "minus", "mtimes", "or", "plus", "polytope",
    "project", "representsa", "splitIntoConvexSets", "supportFunc", "times", "vertices" ]

/-- `op` of `polygon.`, run; `none` for a name this file does not serve. -/
@[noinline, nospecialize]
def handlePolygonOp (dops : DtypeOps 𝕋) (op : String) (req : Json) : Option Resp :=
  match op with
  | "contains" => some (do
      checkFields op req ["pgon", "point", "tol"]
      checkTol op req
      let P ← aux_one dops req
      valueBool (Polygon.containsPoint P (← parseVecFixed dops.readExact 2 (← field req "point"))))
  | "convHull" | "polytope" => some (do
      checkFields op req ["pgon"]
      pure [("P", printVPolytope dops.showExact (Polygon.convHull (← aux_one dops req)))])
  | "empty" => some (do
      checkFields op req []
      pure [aux_set dops (Polygon.empty 𝕋)])
  | "interval" => some (do
      checkFields op req ["pgon"]
      pure [("I", printIntervalVec dops.showExact (Polygon.interval (← aux_one dops req)))])
  -- the predicates
  | "isBounded" => some (do
      checkFields op req ["pgon"]
      let _ ← aux_one dops req
      valueBool true)
  | "isConvex" => some (do
      checkFields op req ["pgon"]
      valueBool (Polygon.isConvex (← aux_one dops req)))
  | "isFullDim" => some (do
      checkFields op req ["pgon"]
      valueBool (Polygon.isFullDim (← aux_one dops req)))
  | "isIntersecting" => some (do
      checkFields op req ["pgon", "pgon2", "tol", "type"]
      checkTol op req
      let (a, b) ← aux_two dops req
      pure [("disjoint", Json.bool (Polygon.isDisjoint a b))])
  | "isequal" => some (do
      checkFields op req ["pgon", "pgon2", "tol"]
      checkTol op req
      let (a, b) ← aux_two dops req
      valueBool (Polygon.isequalPieces a b))
  -- the maps and sums
  | "linComb" => some (aux_binary op dops req Polygon.linComb)
  | "minus" => some (do
      checkFields op req ["pgon", "point"]
      let P ← aux_one dops req
      let p ← parseVecFixed dops.readExact 2 (← field req "point")
      pure [aux_set dops (Polygon.minus P p)])
  | "mtimes" => some (do
      checkFields op req ["pgon", "M"]
      let P ← aux_one dops req
      pure [aux_set dops (Polygon.mtimes (← aux_square dops req) P)])
  | "or" => some (aux_binary op dops req Polygon.or)
  | "plus" => some (aux_binary op dops req Polygon.plus)
  | "project" => some (handlePolygonProject dops req)
  -- the arms from `representsa` on
  | "representsa" => some (do
      checkFields op req ["pgon", "type", "tol"]
      checkTol op req
      checkStrOption op req "type" "emptySet"
      valueBool (Polygon.representsaEmptySet (← aux_one dops req)))
  | "splitIntoConvexSets" => some (do
      checkFields op req ["pgon"]
      let ps := Polygon.splitIntoConvexSets (← aux_one dops req)
      pure [("pieces", Json.arr (ps.map (printVPolytope dops.showExact)).toArray)])
  | "supportFunc" => some (handlePolygonSupportFunc dops req)
  | "times" => some (do
      checkFields op req ["pgon", "factor"]
      let P ← aux_one dops req
      let v ← parseVecFixed dops.readExact 2 (← field req "factor")
      pure [aux_set dops (Polygon.times v P)])
  | "vertices" => some (handlePolygonVertices dops req)
  | _ => none

end CORALean.Oracle


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
