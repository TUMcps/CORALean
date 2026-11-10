import CORALean.ContSet.ContSet.Interfaces
import CORALean.ContSet.EmptySet.Real.Instances
import CORALean.ContSet.Fullspace.Real.Instances
import CORALean.ContSet.Fullspace.Real.Operations.And
import CORALean.ContSet.Fullspace.Real.Operations.Basic
import CORALean.ContSet.Fullspace.Real.Operations.Box
import CORALean.ContSet.Fullspace.Real.Operations.Center
import CORALean.ContSet.Fullspace.Real.Operations.EnclosePoints
import CORALean.ContSet.Fullspace.Real.Operations.IsFullDimTest
import CORALean.ContSet.Fullspace.Real.Operations.Isequal
import CORALean.ContSet.Fullspace.Real.Operations.Lift
import CORALean.ContSet.Fullspace.Real.Operations.Not
import CORALean.ContSet.Fullspace.Real.Operations.Project
import CORALean.ContSet.Fullspace.Real.Operations.ProjectHighDim
import CORALean.ContSet.Fullspace.Real.Operations.Volume
import CORALean.ContSet.Fullspace.Real.Theorems.ToSetNeEmpty
import CORALean.ContSet.Fullspace.Real.Theorems.ToSetNeSingleton
import CORALean.ContSet.HPolytope.Float.Operations.Fullspace
import CORALean.Global.Corners
import CORALean.Examples.Oracle.Ops.EmptySetOps
import CORALean.Examples.Oracle.Ops.IntervalOps
import CORALean.Examples.Oracle.Ops.SetCodec

/-!
# The full-space ops: CORA's `fullspace` methods

As `EmptySetOps.lean`: the full space is its dimension `n`, a result set `F` is `{"n": n}`, and
the adapters call the exact-layer definitions `references/coverage/contSet/fullspace.md` links.
`and` answers the other operand `S` itself, `isIntersecting` reads whether it is
`{"empty":true}`. A box is `I` (`-inf`, `inf`), `radius` and `volume` are `"inf"`. Not served: the
constructor `fullspace`. `vertices` is the `2^n` corners with entries `inf`/`-inf`; `representsa`
answers `emptySet`, `point`, `origin`, `fullspace`. `mtimes` answers the whole space of the image's
dimension, `F` of `{"n": m}`, an outer set, where CORA's differs for a matrix with a zero row.

## Inputs
* none

## Output
* the names of the ops served, or the response fields of an op
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Oracle

open CORALean CORALean.Float CORALean.Real
open Lean (Json)

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every op of this file, without the `fullspace.` prefix. -/
def fullspaceOpNames : List String :=
  [ "Inf", "and", "box", "center", "contains", "convHull", "enclosePoints", "interval",
    "isBounded", "isFullDim", "isIntersecting", "isequal", "lift", "mtimes", "not", "plus",
    "polytope", "project", "projectHighDim", "radius", "representsa", "supportFunc", "vertices",
    "volume" ]

/-- `op` of `fullspace.`, run; `none` for a name this file does not serve. -/
@[noinline, nospecialize]
def handleFullspaceOp (dops : DtypeOps 𝕋) (op : String) (req : Json) : Option Resp :=
  match op with
  | "Inf" => some (do
      checkFields op req ["n"]
      let n ← natField req "n"
      let _ : Fullspace n := Fullspace.Inf n
      pure [("F", printTrivialSet n)])
  | "and" => some (do
      checkFields op req ["n", "S"]
      let n ← natField req "n"
      pure [("S", Fullspace.and_ (Fullspace.Inf n) (← field req "S"))])
  -- the arms from `box` on
  | "box" => some (do
      checkFields op req ["n"]
      let n ← natField req "n"
      let _ := Fullspace.box (Fullspace.Inf n)
      pure [("F", printTrivialSet n)])
  | "center" => some (do
      checkFields op req ["n"]
      let n ← natField req "n"
      let _ := Fullspace.center (Fullspace.Inf n)
      pure [("value", printVec dops.showExact (fun (_ : Fin n) => (FloatOps.zero : 𝕋)))])
  -- the arms from `contains` on
  | "contains" => some (do
      checkFields op req ["n", "S", "tol"]
      checkTol op req
      let n ← natField req "n"
      let _ ← field req "S"
      pure [("contains", Json.bool (Contains.contains (Fullspace.Inf n) (EmptySet.empty n)))])
  | "convHull" => some (do
      checkFields op req ["n", "S"]
      let n ← natField req "n"
      let _ := Fullspace.convHull (Fullspace.Inf n) (← field req "S")
      pure [("F", printTrivialSet n)])
  -- the arms from `enclosePoints` on
  | "enclosePoints" => some (do
      checkFields op req ["n", "points"]
      let n ← natField req "n"
      let dm ← parseMatDyn dops.readExact (← field req "points")
      if dm.r = n then
        let _ : Fullspace n := Fullspace.enclosePoints (p := dm.c) (n := n) fun _ => 0
        pure [("F", printTrivialSet n)]
      else throw s!"enclosePoints: `points` has {dm.r} rows, the dimension is {n}")
  | "interval" => some (do
      checkFields op req ["n"]
      let n ← natField req "n"
      let _ := Fullspace.box (Fullspace.Inf n)
      handleIntervalInf dops req)
  -- the arms from `isBounded` on
  | "isBounded" => some (do
      checkFields op req ["n", "tol"]
      checkTol op req
      valueBool (Fullspace.isBounded (Fullspace.Inf (← natField req "n"))))
  | "isFullDim" => some (do
      checkFields op req ["n", "tol"]
      checkTol op req
      valueBool (Fullspace.isFullDimTest (Fullspace.Inf (← natField req "n"))))
  | "isIntersecting" => some (do
      checkFields op req ["n", "S", "tol", "type"]
      checkTol op req
      let n ← natField req "n"
      let S : OptEmpty (EmptySet n) := if (← operandIsEmpty req) then .empty else .of ⟨⟩
      pure [("disjoint", Json.bool (IsDisjoint.isDisjoint (Fullspace.Inf n) S))])
  -- the arms from `isequal` on
  | "isequal" => some (do
      checkFields op req ["n", "S", "tol"]
      checkTol op req
      let n ← natField req "n"
      let m ← natField (← field req "S") "n"
      if h : m = n then valueBool (Fullspace.isequal (Fullspace.Inf n) (h ▸ Fullspace.Inf m))
      else throw s!"isequal: the dimensions {n} and {m} differ")
  | "lift" => some (do
      checkFields op req ["n", "N", "dims"]
      let n ← natField req "n"
      let ⟨N, d⟩ ← trivialDims req n
      let _ := Fullspace.lift_ (Fullspace.Inf n) N d
      pure [("F", printTrivialSet N)])
  -- `mtimes`: the whole space of the image's dimension, an outer set
  | "mtimes" => some (do
      checkFields op req ["n", "M"]
      let n ← natField req "n"
      let ⟨m, M⟩ ← parseMatColsFixed dops.readExact n (← field req "M")
      let _ := Mtimes.mtimes (𝕄 := Mat 𝕋) (ContSet := fun k => Fullspace k) M (Fullspace.Inf n)
      pure [("F", printTrivialSet m)])
  -- the arms from `not` on
  | "not" => some (do
      checkFields op req ["n"]
      let n ← natField req "n"
      let _ := Fullspace.not (Fullspace.Inf n)
      pure [("E", printTrivialSet n)])
  | "plus" => some (do
      checkFields op req ["n", "S"]
      let n ← natField req "n"
      let m ← natField (← field req "S") "n"
      if h : m = n then
        let _ := Plus.plus (Fullspace.Inf n) (h ▸ Fullspace.Inf m)
        pure [("F", printTrivialSet n)]
      else throw s!"plus: the dimensions {n} and {m} differ")
  -- the arms from `polytope` on
  | "polytope" => some (do
      checkFields op req ["n"]
      let n ← natField req "n"
      pure [("P", printHPolytope dops.showExact (HPolytope.fullspace 𝕋 n))])
  | "project" => some (do
      checkFields op req ["n", "dims"]
      let n ← natField req "n"
      let ⟨m, d⟩ ← indexArrField req "dims" n
      let _ := Fullspace.project (Fullspace.Inf n) d
      pure [("F", printTrivialSet m)])
  -- the arms from `projectHighDim` on
  | "projectHighDim" => some (do
      checkFields op req ["n", "N", "dims"]
      let n ← natField req "n"
      let ⟨N, d⟩ ← trivialDims req n
      let _ := Fullspace.projectHighDim_ (Fullspace.Inf n) N d
      pure [("F", printTrivialSet N)])
  -- `representsa`: the full space is not empty (`toSet_ne_empty`) and, for `n > 0`, no point
  | "representsa" => some (do
      checkFields op req ["n", "type", "tol"]
      checkTol op req
      let n ← natField req "n"
      let F : Fullspace n := Fullspace.Inf n
      match ← strField req "type" with
      | "fullspace" => valueBool true
      | "emptySet" => have _ := Fullspace.toSet_ne_empty F; valueBool false
      | "point" | "origin" =>
        if hn : 0 < n then
          have _ := Fullspace.toSet_ne_singleton hn F; valueBool false
        else throw "representsa: at n = 0 the full space is the single point, not covered"
      | t => throw s!"representsa: `type` must be emptySet, point, origin or fullspace, not `{t}`")
  -- `vertices`: column `l` has `inf` in row `j` where `signEquiv n l j`, else `-inf`; n in 1..20
  | "vertices" => some (do
      checkFields op req ["n"]
      let n ← natField req "n"
      if n = 0 then throw "vertices: needs n >= 1 (`Fullspace.vertices` is stated at n + 1)"
      if n > 20 then throw s!"vertices: n = {n} gives 2^{n} vertices, at most 2^20 are returned"
      pure [("V", Json.mkObj [("rows", Lean.toJson n), ("cols", Lean.toJson (2 ^ n)),
        ("data", Json.arr ((List.finRange n).toArray.flatMap fun j =>
          (List.finRange (2 ^ n)).toArray.map fun l =>
            Json.str (if signEquiv n l j then "inf" else "-inf")))])])
  -- `Fullspace.supportFunc`: `0` at the zero direction, `⊤ = inf` elsewhere, an `EReal`
  | "supportFunc" => some (do
      checkFields op req ["n", "dir", "type"]
      let n ← natField req "n"
      let ty := (fieldOpt req "type").bind (·.getStr?.toOption)
      unless ty.isNone || ty = some "upper" do
        throw "supportFunc: `type` must be `upper`, the definition bounds from above only"
      let d ← parseVecFixed dops.readExact n (← field req "dir")
      let zero := (List.finRange n).all fun i => dops.showExact (d i) = dops.showExact FloatOps.zero
      pure [("value", Json.str (if zero then dops.showExact FloatOps.zero else "inf"))])
  | "radius" => some (do
      checkFields op req ["n"]
      let _ := Fullspace.radius (Fullspace.Inf (← natField req "n"))
      pure [("value", Json.str "inf")])
  -- the arms from `volume` on
  | "volume" => some (do
      checkFields op req ["n"]
      let _ := Fullspace.volume (Fullspace.Inf (← natField req "n"))
      pure [("value", Json.str "inf")])
  | _ => none

end CORALean.Oracle


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
