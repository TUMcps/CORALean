import CORALean.ContSet.Conversion.Float.Operations.Basic
import CORALean.ContSet.Conversion.Float.Operations.VPolytope_to_ConZonotope
import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_HPolytope
import CORALean.ContSet.HPolytope.Float.Operations.Basic
import CORALean.ContSet.HPolytope.Float.Operations.CartProd
import CORALean.ContSet.HPolytope.Float.Operations.CompactAlignedIneq
import CORALean.ContSet.HPolytope.Float.Operations.CompactAtoAe
import CORALean.ContSet.HPolytope.Float.Operations.CompactZeros
import CORALean.ContSet.HPolytope.Float.Operations.EmptySet
import CORALean.ContSet.HPolytope.Float.Operations.Fullspace
import CORALean.ContSet.HPolytope.Float.Operations.Intersection
import CORALean.ContSet.HPolytope.Float.Operations.Isequal
import CORALean.ContSet.HPolytope.Float.Operations.Lift
import CORALean.ContSet.HPolytope.Float.Operations.MinkDiffOf
import CORALean.ContSet.HPolytope.Float.Operations.NormalizeConstraints
import CORALean.ContSet.HPolytope.Float.Operations.Not
import CORALean.ContSet.HPolytope.Float.Operations.Origin
import CORALean.ContSet.HPolytope.Float.Operations.ProjectHighDim
import CORALean.ContSet.HPolytope.Float.Operations.ReduceOverDomain
import CORALean.ContSet.HPolytope.Float.Operations.RepresentsaFullspace
import CORALean.ContSet.Interval.Float.Operations.BoundDot
import CORALean.ContSet.VPolytope.Float.Operations.CenterBox
import CORALean.ContSet.VPolytope.Float.Operations.ConvHull
import CORALean.ContSet.VPolytope.Float.Operations.EnclosePoints
import CORALean.ContSet.VPolytope.Float.Operations.Intersection
import CORALean.ContSet.VPolytope.Float.Operations.IsFullDim
import CORALean.ContSet.VPolytope.Float.Operations.Mtimes
import CORALean.ContSet.VPolytope.Float.Operations.Plus
import CORALean.ContSet.VPolytope.Float.Operations.Project
import CORALean.ContSet.VPolytope.Float.Operations.ProjectHighDim
import CORALean.ContSet.VPolytope.Float.Operations.SupportBound
import CORALean.Examples.Oracle.Ops.SetCodec
import CORALean.Specification.Instances

/-!
# The polytope ops: CORA's `polytope` methods

Adapters over the float definitions `references/coverage/contSet/polytope.md` links. CORALean has
two classes for the two forms, so an operand `P`, `P2` is read by its keys, `{"V","E"}` vertex
form (`VPolytope`), `{"A","b",...}` halfspace form (`HPolytope`); an op names the form it takes.
A result is `P`, a box `I`, a constrained zonotope `cZ`, a Boolean or a bound `value`. `minkDiff`
takes the subtrahend as a box `I` or a zonotope `Z`, its support bounds the certificates
`HPolytope.minkDiffOf` asks for. Not served: the ops whose Lean definition needs bounds or rows CORA
has no argument for (`compact_` `redundant`, `constraints`, `vertices`, the other-form
`convHull`/`mtimes`/`plus`), the classes without a wire format.

## Inputs
* `dops` – dtype operations
* `req` – request

## Output
* response fields or an error message
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-November-2026
-- Last update:   07-November-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Oracle

open CORALean CORALean.Float
open Lean (Json)

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

private def aux_hSet (dops : DtypeOps 𝕋) {n : Nat} (P : HPolytope 𝕋 (Vec 𝕋 n)) : String × Json :=
  ("P", printHPolytope dops.showExact P)

private def aux_vSet (dops : DtypeOps 𝕋) {n : Nat} (P : VPolytope (Vec 𝕋 n)) : String × Json :=
  ("P", printVPolytope dops.showExact P)

/-- Whether the operand `name` is in vertex form. -/
private def aux_isV (req : Json) (name : String) : Bool :=
  match fieldOpt req name with
  | some j => (fieldOpt j "V").isSome
  | none => false

/-- The halfspace polytope in field `name`, a vertex polytope refused. -/
private def aux_h (op : String) (dops : DtypeOps 𝕋) (req : Json) (name : String) :
    Except String (DynHPolytope 𝕋) := do
  if aux_isV req name then
    throw s!"{op}: `{name}` is a vertex polytope, CORALean's float {op} takes a halfspace polytope"
  parseHPolytope dops.readExact (← field req name)

/-- The vertex polytope in field `name`, a halfspace polytope refused. -/
private def aux_v (op : String) (dops : DtypeOps 𝕋) (req : Json) (name : String) :
    Except String (DynVPolytope 𝕋) := do
  unless aux_isV req name do
    throw s!"{op}: `{name}` is a halfspace polytope, CORALean's float {op} takes a vertex polytope \
      `{"{"}\"V\",\"E\"{"}"}`"
  parseVPolytope dops.readExact (← field req name)

/-- The second operand of a test: a box `I` or a zonotope `Z`, one of the two. -/
private inductive Probe (𝕋 : Type) (n : Nat) where
  | box : Interval (Vec 𝕋 n) → Probe 𝕋 n
  | zono : Zonotope (Vec 𝕋 n) → Probe 𝕋 n

private def aux_probe (op : String) (dops : DtypeOps 𝕋) (req : Json) (n : Nat) :
    Except String (Probe 𝕋 n) :=
  match fieldOpt req "I", fieldOpt req "Z" with
  | some j, none => do pure (.box (← parseIntervalVecFixed dops.readExact n j))
  | none, some j => do pure (.zono (← parseZonotopeFixed dops.readExact n j))
  | _, _ => throw s!"{op}: give exactly one of `I` (a box) and `Z` (a zonotope)"


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `polytope.contains`: `P` certified to contain the box `I` or the zonotope `Z`. -/
def handlePolyContains (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "contains" req ["P", "I", "Z", "tol", "type"]
  checkTol "contains" req
  let d ← aux_h "contains" dops req "P"
  match ← aux_probe "contains" dops req d.n with
  | .box I => pure [("contains", Json.bool (Contains.contains d.P I))]
  | .zono Z => pure [("contains", Json.bool (Contains.contains d.P Z))]

/-- `polytope.isIntersecting`: `disjoint = true` certifies `P` and `I` or `Z` share no point. -/
def handlePolyIsIntersecting (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "isIntersecting" req ["P", "I", "Z", "tol", "type"]
  checkTol "isIntersecting" req
  let d ← aux_h "isIntersecting" dops req "P"
  match ← aux_probe "isIntersecting" dops req d.n with
  | .box I => pure [("disjoint", Json.bool (IsDisjoint.isDisjoint d.P I))]
  | .zono Z => pure [("disjoint", Json.bool (IsDisjoint.isDisjoint d.P Z))]

/-- `polytope.and`: halfspace form, `HPolytope.intersection`; vertex form,
`VPolytope.intersection`. -/
def handlePolyAnd (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "and" req ["P", "P2"]
  if aux_isV req "P" then
    let a ← aux_v "and" dops req "P"
    let b ← parseVPolytopeFixed dops.readExact a.n (← field req "P2")
    pure [aux_vSet dops (VPolytope.intersection a.P b)]
  else
    let a ← aux_h "and" dops req "P"
    let b ← parseHPolytopeFixed dops.readExact a.n (← field req "P2")
    pure [aux_hSet dops (HPolytope.intersection a.P b)]

/-- `polytope.lift`: `P` in `N` dimensions, coordinate `k` at `dims[k]`, `HPolytope.lift_`. -/
def handlePolyLift (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "lift" req ["P", "N", "dims"]
  let d ← aux_h "lift" dops req "P"
  let N ← natField req "N"
  let ⟨m, dims⟩ ← indexArrField req "dims" N
  if h : m = d.n then
    pure [aux_hSet dops (HPolytope.lift_ d.P (fun i => dims (Fin.cast h.symm i)))]
  else throw s!"lift: `dims` has {m} entries, the polytope has dimension {d.n}"

/-- `polytope.projectHighDim`: coordinate `k` written at `dims[k]` of `N` dimensions. -/
def handlePolyProjectHighDim (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "projectHighDim" req ["P", "N", "dims"]
  let N ← natField req "N"
  let build (n m : Nat) (dims : Fin m → Fin N) : Except String (Fin n → Fin N) :=
    if h : m = n then pure fun i => dims (Fin.cast h.symm i)
    else throw s!"projectHighDim: `dims` has {m} entries, the polytope has dimension {n}"
  if aux_isV req "P" then
    let d ← aux_v "projectHighDim" dops req "P"
    let ⟨m, dims⟩ ← indexArrField req "dims" N
    pure [aux_vSet dops (VPolytope.projectHighDim d.P (← build d.n m dims))]
  else
    let d ← aux_h "projectHighDim" dops req "P"
    let ⟨m, dims⟩ ← indexArrField req "dims" N
    pure [aux_hSet dops (HPolytope.projectHighDim d.P (← build d.n m dims))]

/-- `polytope.enclosePoints`: the points, one per column, as a vertex polytope. -/
def handlePolyEnclosePoints (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "enclosePoints" req ["points", "method"]
  checkStrOption "enclosePoints" req "method" "outer"
  let dm ← parseMatDyn dops.readExact (← field req "points")
  pure [aux_vSet dops (VPolytope.enclosePoints (N := dm.c) (n := dm.r) (fun l i => dm.M i l))]

/-- `polytope.supportFunc`: the upper bound of `dir · x` over a vertex polytope,
`VPolytope.boundDot`. -/
def handlePolySupportFunc (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "supportFunc" req ["P", "dir", "type"]
  checkStrOption "supportFunc" req "type" "upper"
  let d ← aux_v "supportFunc" dops req "P"
  let a ← parseVecFixed dops.readExact d.n (← field req "dir")
  valueScalar dops.showExact (d.P.boundDot (c := rowFunctional a) a fun _ => rfl).val

/-- `polytope.compact`: the halfspace polytope with its rows unit-normalised over the box `dom`
(`p` Newton steps), then `zeros` drops the zero rows, `aligned` the dominated rows of equal normal,
`AtoAe` turns inverted pairs into equalities. `redundant` needs a linear program. -/
def handlePolyCompact (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "compact" req ["P", "method", "tol", "dom", "p"]
  checkTol "compact" req
  let d ← aux_h "compact" dops req "P"
  let dom ← parseIntervalVecFixed dops.readExact d.n (← field req "dom")
  let p ← natField req "p"
  match ← strField req "method" with
  | "zeros" => pure [aux_hSet dops (HPolytope.compactZeros p d.P dom)]
  | "aligned" => pure [aux_hSet dops (HPolytope.compactAlignedIneq p d.P dom)]
  | "AtoAe" => pure [aux_hSet dops (HPolytope.compactAtoAe p d.P dom)]
  | m => throw s!"compact: `method` must be zeros, aligned or AtoAe, not `{m}`"

/-- A scalar field read exactly into the dtype. -/
private def aux_scalar (dops : DtypeOps 𝕋) (req : Json) (name : String) : Except String 𝕋 := do
  dops.readExact name (← scalarField req name)

/-- `polytope.not`: `-a x <= -b - eps` for a polytope of the single inequality `a x <= b`,
`HPolytope.not`; any other polytope is refused, as the Lean definition answers `none`. -/
def handlePolyNot (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "not" req ["P", "eps"]
  let d ← aux_h "not" dops req "P"
  let ε ← aux_scalar dops req "eps"
  match HPolytope.not d.P ε with
  | some Q => pure [aux_hSet dops Q]
  | none => throw "not: only a polytope of exactly one inequality and no equality is complemented"

/-- `polytope.normalizeConstraints`: every row divided by its right-hand side's magnitude over the
box `dom`, `HPolytope.normalizeConstraints`. -/
def handlePolyNormalizeConstraints (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "normalizeConstraints" req ["P", "dom", "type"]
  checkStrOption "normalizeConstraints" req "type" "b"
  let d ← aux_h "normalizeConstraints" dops req "P"
  let dom ← parseIntervalVecFixed dops.readExact d.n (← field req "dom")
  pure [aux_hSet dops (HPolytope.normalizeConstraints d.P dom)]

/-- `polytope.reduceOverDomain`: the single halfspace over the box `dom` (`p` Newton steps),
`type` `outer` or `inner`, `HPolytope.reduceOverDomain`. -/
def handlePolyReduceOverDomain (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "reduceOverDomain" req ["P", "dom", "p", "type"]
  let d ← aux_h "reduceOverDomain" dops req "P"
  let dom ← parseIntervalVecFixed dops.readExact d.n (← field req "dom")
  let p ← natField req "p"
  match fieldOpt req "type" with
  | none => pure [aux_hSet dops (HPolytope.reduceOverDomain p d.P dom true)]
  | some _ =>
    match ← strField req "type" with
    | "outer" => pure [aux_hSet dops (HPolytope.reduceOverDomain p d.P dom true)]
    | "inner" => pure [aux_hSet dops (HPolytope.reduceOverDomain p d.P dom false)]
    | t => throw s!"reduceOverDomain: `type` must be outer or inner, not `{t}`"

/-- `polytope.minkDiff`: `P` minus a box `I` or a zonotope `Z`, each row lowered by the
subtrahend's support bound in that row's direction, `HPolytope.minkDiffOf`. -/
def handlePolyMinkDiff (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "minkDiff" req ["P", "I", "Z"]
  let d ← aux_h "minkDiff" dops req "P"
  match ← aux_probe "minkDiff" dops req d.n with
  | .box I =>
    pure [aux_hSet dops (d.P.minkDiffOf I.toSet fun i =>
      I.boundDot (c := Real.HPolytope.rowLin (toRealMat d.P.A) i) (d.P.A i) fun _ => rfl)]
  | .zono Z =>
    pure [aux_hSet dops (d.P.minkDiffOf Z.toSet fun i =>
      Z.boundDot (c := Real.HPolytope.rowLin (toRealMat d.P.A) i) (d.P.A i) fun _ => rfl)]

/-- Every op of this file, without the `polytope.` prefix. -/
def polytopeOpNames : List String :=
  [ "Inf", "and", "box", "cartProd", "center", "compact", "conZonotope", "contains", "convHull",
    "empty", "enclosePoints", "interval", "isBounded", "isFullDim", "isIntersecting", "isequal",
    "lift", "minus", "mtimes", "or", "origin", "plus", "project", "projectHighDim", "representsa",
    "supportFunc", "zonotope", "ellipsoid", "zonoBundle", "not", "normalizeConstraints",
    "reduceOverDomain", "minkDiff" ]

/-- `op` of `polytope.`, run; `none` for a name this file does not serve. -/
@[noinline, nospecialize]
def handlePolytopeOp (dops : DtypeOps 𝕋) (op : String) (req : Json) : Option Resp :=
  match op with
  | "Inf" => some (do
      checkFields op req ["n"]
      pure [aux_hSet dops (HPolytope.fullspace 𝕋 (← natField req "n"))])
  | "empty" => some (do
      checkFields op req ["n"]
      pure [aux_hSet dops (HPolytope.emptySet 𝕋 (← natField req "n"))])
  | "origin" => some (do
      checkFields op req ["n"]
      pure [aux_hSet dops (HPolytope.origin (𝕋 := 𝕋) (← natField req "n"))])
  -- the arms from `and` on
  | "and" => some (handlePolyAnd dops req)
  | "box" | "interval" => some (do
      checkFields op req ["P"]
      let d ← aux_v op dops req "P"
      pure [("I", printIntervalVec dops.showExact (VPolytope.interval d.P))])
  | "cartProd" => some (do
      checkFields op req ["P", "P2"]
      let a ← aux_h op dops req "P"
      let b ← aux_h op dops req "P2"
      pure [aux_hSet dops (HPolytope.cartProd a.P b.P)])
  -- the arms from `center` on
  | "compact" => some (handlePolyCompact dops req)
  | "center" => some (do
      checkFields op req ["P"]
      let d ← aux_v op dops req "P"
      pure [("I", printIntervalVec dops.showExact (VPolytope.centerBox d.P))])
  | "conZonotope" => some (do
      checkFields op req ["P"]
      let d ← aux_v op dops req "P"
      pure [("cZ", printConZonotope dops.showExact (VPolytope.conZonotope d.P))])
  | "contains" => some (handlePolyContains dops req)
  | "convHull" | "or" => some (do
      checkFields op req ["P", "P2"]
      let a ← aux_v op dops req "P"
      let b ← parseVPolytopeFixed dops.readExact a.n (← field req "P2")
      pure [aux_vSet dops (VPolytope.convHull a.P b)])
  -- the arms from `enclosePoints` on
  | "enclosePoints" => some (handlePolyEnclosePoints dops req)
  | "isBounded" => some (do
      checkFields op req ["P", "tol"]
      checkTol op req
      let _ ← aux_v op dops req "P"
      valueBool true)
  | "isFullDim" => some (do
      checkFields op req ["P", "tol"]
      checkTol op req
      let d ← aux_v op dops req "P"
      valueBool (VPolytope.isFullDim d.P))
  -- the arms from `isIntersecting` on
  | "isIntersecting" => some (handlePolyIsIntersecting dops req)
  | "not" => some (handlePolyNot dops req)
  | "normalizeConstraints" => some (handlePolyNormalizeConstraints dops req)
  | "reduceOverDomain" => some (handlePolyReduceOverDomain dops req)
  | "minkDiff" => some (handlePolyMinkDiff dops req)
  | "isequal" => some (do
      checkFields op req ["P", "P2", "tol"]
      checkTol op req
      let a ← aux_h op dops req "P"
      let b ← parseHPolytopeFixed dops.readExact a.n (← field req "P2")
      valueBool (HPolytope.isequal a.P b))
  | "lift" => some (handlePolyLift dops req)
  | "minus" => some (do
      checkFields op req ["P", "v"]
      let d ← aux_h op dops req "P"
      let v ← parseVecFixed dops.readExact d.n (← field req "v")
      pure [aux_hSet dops (HPolytope.minus d.P v)])
  -- the arms from `mtimes` on
  | "mtimes" => some (do
      checkFields op req ["P", "M"]
      let d ← aux_v op dops req "P"
      let ⟨_, M⟩ ← parseMatColsFixed dops.readExact d.n (← field req "M")
      pure [aux_vSet dops (VPolytope.mtimes M d.P)])
  | "plus" => some (do
      checkFields op req ["P", "P2"]
      let a ← aux_v op dops req "P"
      let b ← parseVPolytopeFixed dops.readExact a.n (← field req "P2")
      pure [aux_vSet dops (VPolytope.plus a.P b)])
  -- the arms from `project` on
  | "project" => some (do
      checkFields op req ["P", "dims"]
      let d ← aux_v op dops req "P"
      let ⟨_, dims⟩ ← indexArrField req "dims" d.n
      pure [aux_vSet dops (VPolytope.project d.P dims)])
  | "projectHighDim" => some (handlePolyProjectHighDim dops req)
  | "representsa" => some (do
      checkFields op req ["P", "type", "tol"]
      checkTol op req
      checkStrOption op req "type" "fullspace"
      let d ← aux_h op dops req "P"
      valueBool (HPolytope.representsaFullspace d.P))
  -- the arms from `supportFunc` on
  | "supportFunc" => some (handlePolySupportFunc dops req)
  -- the conversions of a vertex polytope
  | "zonotope" | "zonoBundle" => some (do
      checkFields op req ["P"]
      let d ← aux_v op dops req "P"
      if op = "zonotope" then
        pure [("Z", printZonotope dops.showExact (VPolytope.zonotope d.P))]
      else pure [("zB", printZonoBundle dops.showExact (VPolytope.zonoBundle d.P))])
  | "ellipsoid" => some (do
      checkFields op req ["P", "sigma"]
      let d ← aux_v op dops req "P"
      let σ ← dops.readExact "sigma" (← scalarField req "sigma")
      pure [("E", printEllipsoid dops.showExact (VPolytope.ellipsoid d.P σ))])
  | _ => none

end CORALean.Oracle


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
