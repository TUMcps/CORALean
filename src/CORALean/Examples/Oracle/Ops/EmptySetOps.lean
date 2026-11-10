import CORALean.ContSet.ContSet.Interfaces
import CORALean.ContSet.EmptySet.Real.Instances
import CORALean.ContSet.EmptySet.Real.Operations.And
import CORALean.ContSet.EmptySet.Real.Operations.Basic
import CORALean.ContSet.EmptySet.Real.Operations.Center
import CORALean.ContSet.EmptySet.Real.Operations.HPolytope
import CORALean.ContSet.EmptySet.Real.Operations.IsBounded
import CORALean.ContSet.EmptySet.Real.Operations.IsFullDimTest
import CORALean.ContSet.EmptySet.Real.Operations.Isequal
import CORALean.ContSet.EmptySet.Real.Operations.Lift
import CORALean.ContSet.EmptySet.Real.Operations.Not
import CORALean.ContSet.EmptySet.Real.Operations.Project
import CORALean.ContSet.EmptySet.Real.Operations.ProjectHighDim
import CORALean.ContSet.HPolytope.Float.Operations.EmptySet
import CORALean.ContSet.Interval.Float.Operations.Basic
import CORALean.ContSet.EmptySet.Real.Operations.SupportFunc
import CORALean.ContSet.EmptySet.Real.Operations.Vertices
import CORALean.ContSet.EmptySet.Real.Theorems.ToSetNeSingleton
import CORALean.ContSet.EmptySet.Real.Theorems.ToSetNeUniv
import CORALean.Examples.Oracle.Ops.IntervalOps
import CORALean.Examples.Oracle.Ops.SetCodec

/-!
# The empty-set ops: CORA's `emptySet` methods

`EmptySet n` holds no scalar and its operations compute nothing numeric, so the adapters call the
exact-layer definitions `references/coverage/contSet/emptySet.md` links. The set is its dimension
`n`, a result set `E` is `{"n": n}`. The other operand `S` is any wire object; only its dimension
(`n`, for `isequal`, `plus`) or `{"empty":true}` (for `contains`, `isIntersecting`, CORA's
`isemptyobject(S)`) enters. Not served: the constructor `emptySet`.

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

/-- Every op of this file, without the `emptySet.` prefix. -/
def emptySetOpNames : List String :=
  [ "and", "center", "contains", "convHull", "empty", "interval", "isBounded", "isFullDim",
    "isIntersecting", "isequal", "lift", "mtimes", "not", "plus", "polytope", "project",
    "projectHighDim", "radius", "representsa", "supportFunc", "vertices", "volume" ]

/-- `op` of `emptySet.`, run; `none` for a name this file does not serve. -/
@[noinline, nospecialize]
def handleEmptySetOp (dops : DtypeOps 𝕋) (op : String) (req : Json) : Option Resp :=
  match op with
  | "empty" => some (do
      checkFields op req ["n"]
      let n ← natField req "n"
      let _ : EmptySet n := EmptySet.empty n
      pure [("E", printTrivialSet n)])
  | "and" => some (do
      checkFields op req ["n", "S"]
      let n ← natField req "n"
      let _ := EmptySet.and_ (S := Json) (EmptySet.empty n) (← field req "S")
      pure [("E", printTrivialSet n)])
  -- the arms from `center` on
  | "center" => some (do
      checkFields op req ["n"]
      let n ← natField req "n"
      match EmptySet.center (EmptySet.empty n) with
      | none => pure [("value", Json.null)]
      | some _ => throw "center: unreachable, CORALean's emptySet has no center")
  | "contains" => some (do
      checkFields op req ["n", "S", "tol"]
      checkTol op req
      let n ← natField req "n"
      let S : OptEmpty (EmptySet n) := if (← operandIsEmpty req) then .empty else .of ⟨⟩
      pure [("contains", Json.bool (Contains.contains (EmptySet.empty n) S))])
  -- the arms from `convHull` on
  | "convHull" => some (do
      checkFields op req ["n", "S"]
      let S ← field req "S"
      pure [("S", EmptySet.convHull (EmptySet.empty (← natField req "n")) S)])
  | "interval" => some (do
      checkFields op req ["n"]
      handleIntervalConst "empty" dops req)
  | "isBounded" => some (do
      checkFields op req ["n", "tol"]
      checkTol op req
      valueBool (EmptySet.isBounded (EmptySet.empty (← natField req "n"))))
  -- the arms from `isFullDim` on
  | "isFullDim" => some (do
      checkFields op req ["n", "tol"]
      checkTol op req
      valueBool (EmptySet.isFullDimTest (EmptySet.empty (← natField req "n"))))
  | "isIntersecting" => some (do
      checkFields op req ["n", "S", "tol", "type"]
      checkTol op req
      let n ← natField req "n"
      let _ ← field req "S"
      pure [("disjoint", Json.bool (IsDisjoint.isDisjoint (EmptySet.empty n) (EmptySet.empty n)))])
  -- the arms from `isequal` on
  | "isequal" => some (do
      checkFields op req ["n", "S", "tol"]
      checkTol op req
      let n ← natField req "n"
      let m ← natField (← field req "S") "n"
      if h : m = n then valueBool (EmptySet.isequal (EmptySet.empty n) (h ▸ EmptySet.empty m))
      else throw s!"isequal: the dimensions {n} and {m} differ")
  | "lift" => some (do
      checkFields op req ["n", "N", "dims"]
      let n ← natField req "n"
      let ⟨N, d⟩ ← trivialDims req n
      let _ := EmptySet.lift_ (EmptySet.empty n) N d
      pure [("E", printTrivialSet N)])
  -- the arms from `mtimes` on
  | "mtimes" => some (do
      checkFields op req ["n", "M"]
      let n ← natField req "n"
      let ⟨m, M⟩ ← parseMatColsFixed dops.readExact n (← field req "M")
      -- the instance, which ignores `M`
      let _ := Mtimes.mtimes (𝕄 := Mat 𝕋) (S := fun k => EmptySet k) M (EmptySet.empty n)
      pure [("E", printTrivialSet m)])
  -- `EmptySet.supportFunc` is `⊥ = -inf`, a noncomputable `EReal`: printed as that constant
  | "supportFunc" => some (do
      checkFields op req ["n", "dir", "type"]
      let n ← natField req "n"
      let ty := (fieldOpt req "type").bind (·.getStr?.toOption)
      unless ty.isNone || ty = some "upper" do
        throw "supportFunc: `type` must be `upper`, the definition bounds from above only"
      let _ ← parseVecFixed dops.readExact n (← field req "dir")
      pure [("value", Json.str "-inf")])
  -- the arms from `not` on
  | "not" => some (do
      checkFields op req ["n"]
      let n ← natField req "n"
      let _ := EmptySet.not (EmptySet.empty n)
      pure [("F", printTrivialSet n)])
  | "plus" => some (do
      checkFields op req ["n", "S"]
      let n ← natField req "n"
      let m ← natField (← field req "S") "n"
      if h : m = n then
        let _ := Plus.plus (EmptySet.empty n) (h ▸ EmptySet.empty m)
        pure [("E", printTrivialSet n)]
      else throw s!"plus: the dimensions {n} and {m} differ")
  -- the arms from `polytope` on
  | "polytope" => some (do
      checkFields op req ["n"]
      let n ← natField req "n"
      pure [("P", printHPolytope dops.showExact (HPolytope.emptySet 𝕋 n))])
  | "project" => some (do
      checkFields op req ["n", "dims"]
      let n ← natField req "n"
      let ⟨m, d⟩ ← indexArrField req "dims" n
      let _ := EmptySet.project (EmptySet.empty n) d
      pure [("E", printTrivialSet m)])
  -- the arms from `projectHighDim` on
  | "projectHighDim" => some (do
      checkFields op req ["n", "N", "dims"]
      let n ← natField req "n"
      let ⟨N, d⟩ ← trivialDims req n
      let _ := EmptySet.projectHighDim_ (EmptySet.empty n) N d
      pure [("E", printTrivialSet N)])
  -- `representsa`: `emptySet` holds, the set is no point, origin or full space (proved)
  | "representsa" => some (do
      checkFields op req ["n", "type", "tol"]
      checkTol op req
      let n ← natField req "n"
      let E : EmptySet n := EmptySet.empty n
      match ← strField req "type" with
      | "emptySet" => valueBool true
      | "point" => have _ := EmptySet.toSet_ne_singleton E; valueBool false
      | "origin" => have _ := EmptySet.toSet_ne_singleton E; valueBool false
      | "fullspace" => have _ := EmptySet.toSet_ne_univ E; valueBool false
      | t => throw s!"representsa: `type` must be emptySet, point, origin or fullspace, not `{t}`")
  | "radius" => some (do
      checkFields op req ["n"]
      let _ := EmptySet.radius (EmptySet.empty (← natField req "n"))
      pure [("value", Json.str (dops.showExact (FloatOps.zero : 𝕋)))])
  -- the arms from `vertices` on
  | "vertices" => some (do
      checkFields op req ["n"]
      let n ← natField req "n"
      let _ := EmptySet.vertices (EmptySet.empty n)
      pure [("V", Json.mkObj [("rows", Lean.toJson n), ("cols", Lean.toJson 0),
        ("data", Json.arr #[])])])
  | "volume" => some (do
      checkFields op req ["n"]
      let _ := EmptySet.volume (EmptySet.empty (← natField req "n"))
      pure [("value", Json.str (dops.showExact (FloatOps.zero : 𝕋)))])
  | _ => none

end CORALean.Oracle


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
