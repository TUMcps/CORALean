import CORALean.ContSet.Conversion.Float.Operations.Ellipsoid_to_Zonotope
import CORALean.ContSet.Ellipsoid.Float.Operations.AndPoint
import CORALean.ContSet.Ellipsoid.Float.Operations.Basic
import CORALean.ContSet.Ellipsoid.Float.Operations.CartProd
import CORALean.ContSet.Ellipsoid.Float.Operations.ContainsPoint
import CORALean.ContSet.Ellipsoid.Float.Operations.EllipsoidNormUb
import CORALean.ContSet.Ellipsoid.Float.Operations.EnclosePointsCov
import CORALean.ContSet.Ellipsoid.Float.Operations.ExcludesPoint
import CORALean.ContSet.Ellipsoid.Float.Operations.IntersectStripGollamudi
import CORALean.ContSet.Ellipsoid.Float.Operations.IntersectStripLiu
import CORALean.ContSet.Ellipsoid.Float.Operations.IsGoodDir
import CORALean.ContSet.Zonotope.Float.Operations.BasisInverse
import CORALean.ContSet.Ellipsoid.Float.Operations.BoxRadius
import CORALean.ContSet.Ellipsoid.Float.Operations.CartProdVec
import CORALean.ContSet.Ellipsoid.Float.Operations.IsBigger
import CORALean.ContSet.Ellipsoid.Float.Operations.IsFullDim
import CORALean.ContSet.Ellipsoid.Float.Operations.Isequal
import CORALean.ContSet.Ellipsoid.Float.Operations.Mtimes
import CORALean.ContSet.Ellipsoid.Float.Operations.NormUb
import CORALean.ContSet.Ellipsoid.Float.Operations.Origin
import CORALean.ContSet.Ellipsoid.Float.Operations.Project
import CORALean.ContSet.Ellipsoid.Float.Operations.Radius
import CORALean.ContSet.Ellipsoid.Float.Operations.Reindex
import CORALean.ContSet.Ellipsoid.Float.Operations.RepresentsaOrigin
import CORALean.ContSet.Ellipsoid.Float.Operations.RepresentsaPoint
import CORALean.ContSet.Ellipsoid.Float.Operations.Vertices
import CORALean.Examples.Oracle.Ops.SetCodec

/-!
# The ellipsoid ops: CORA's `ellipsoid` methods

Thin adapters over the float definitions `references/coverage/contSet/ellipsoid.md` links.
Operands are `E`, `E2` (`{"Q","q","E"}`); a set result is `E`, a vertex list `V`, a vector or a
scalar `value`. `norm`, `vertices` take the Newton steps `k`, `radius` the steps `p`. The ops whose
float definition takes a certificate read it as optional fields, the library's candidate
(`Zonotope.basisInverse`, `Ellipsoid.boxRadius`) where CORA has none. Not served: `enclose` (an
SDP hull), `generators`, `empty`, `isIntersecting`, `supportFunc`, `volume`, `plus`, `minkDiff`, ...

## Inputs
* `dops` – dtype operations
* `req` – request

## Output
* response fields or an error message
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Oracle

open CORALean CORALean.Float
open Lean (Json)

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

private def aux_set (dops : DtypeOps 𝕋) {n : Nat} (E : Ellipsoid 𝕋 n) : String × Json :=
  ("E", printEllipsoid dops.showExact E)

/-- A test of one ellipsoid. -/
private def aux_test (op : String) (dops : DtypeOps 𝕋) (req : Json)
    (f : {n : Nat} → Ellipsoid 𝕋 n → Bool) : Resp := do
  checkFields op req ["E", "tol"]
  checkTol op req
  let d ← parseEllipsoid dops.readExact (← field req "E")
  valueBool (f d.E)


/-- `Q⁻¹ r` by `Zonotope.basisInverse`, the default witness (a proposal, checked later). -/
private def aux_solve {n : Nat} (E : Ellipsoid 𝕋 n) (r : Vec 𝕋 n) : Vec 𝕋 n :=
  let Qi := Zonotope.basisInverse E.Q
  fun i => dotUp (fun l => Qi i l) r

/-- `p - q`, rounded down. -/
private def aux_diff {n : Nat} (E : Ellipsoid 𝕋 n) (p : Vec 𝕋 n) : Vec 𝕋 n :=
  fun i => subDown (p i) (E.q i)

/-- The optional vector field `name`, else `dflt`. -/
private def aux_vecOpt (dops : DtypeOps 𝕋) (req : Json) (name : String) (n : Nat)
    (dflt : Vec 𝕋 n) : Except String (Vec 𝕋 n) :=
  match fieldOpt req name with
  | none => pure dflt
  | some j => parseVecFixed dops.readExact n j

/-- A scalar field read exactly into the dtype. -/
private def aux_scalar (dops : DtypeOps 𝕋) (req : Json) (name : String) : Except String 𝕋 := do
  dops.readExact name (← scalarField req name)

/-- The box half-widths: the optional field `s`, else `Ellipsoid.boxRadius k`. -/
private def aux_boxS (dops : DtypeOps 𝕋) (req : Json) {n : Nat} (E : Ellipsoid 𝕋 n) :
    Except String (Vec 𝕋 n) := do
  match fieldOpt req "s" with
  | some j => parseVecFixed dops.readExact n j
  | none => pure (Ellipsoid.boxRadius (← natField req "k") E)

/-- A square `n x n` matrix field. -/
private def aux_square (dops : DtypeOps 𝕋) (req : Json) (name : String) (n : Nat) :
    Except String (Mat 𝕋 n n) := do
  let ⟨r, M⟩ ← parseMatColsFixed dops.readExact n (← field req name)
  if h : r = n then pure (h ▸ M) else throw s!"`{name}` has {r} rows, expected {n}"

/-- `ellipsoid.cartProd` of two ellipsoids: `Ellipsoid.cartProd`, box half-widths `s1`, `s2`
(default `boxRadius k`) and `sigma` with `n + m ≤ sigma²`. -/
private def aux_cartProd2 (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "cartProd" req ["E", "E2", "s1", "s2", "k", "sigma"]
  let d ← parseEllipsoid dops.readExact (← field req "E")
  let d2 ← parseEllipsoid dops.readExact (← field req "E2")
  let s₁ ← match fieldOpt req "s1" with
    | some j => parseVecFixed dops.readExact d.n j
    | none => pure (Ellipsoid.boxRadius (← natField req "k") d.E)
  let s₂ ← match fieldOpt req "s2" with
    | some j => parseVecFixed dops.readExact d2.n j
    | none => pure (Ellipsoid.boxRadius (← natField req "k") d2.E)
  pure [aux_set dops (Ellipsoid.cartProd d.E d2.E s₁ s₂ (← aux_scalar dops req "sigma"))]

/-- `ellipsoid.intersectStrip`: the Gollamudi or the Liu update for one strip. -/
private def aux_strip (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "intersectStrip" req ["E", "c", "phi", "V", "y", "lam", "k", "method"]
  let d ← parseEllipsoid dops.readExact (← field req "E")
  let c ← parseVecFixed dops.readExact d.n (← field req "c")
  let k ← natField req "k"
  let y ← aux_scalar dops req "y"
  let lam ← aux_scalar dops req "lam"
  match ← strField req "method" with
  | "Gollamudi" => pure [aux_set dops
      (Ellipsoid.intersectStripGollamudi k d.E c (← aux_scalar dops req "phi") y lam)]
  | "Liu2016" => pure [aux_set dops
      (Ellipsoid.intersectStripLiu k d.E c (← aux_scalar dops req "V") y lam)]
  | m => throw s!"intersectStrip: `method` must be Gollamudi or Liu2016, not `{m}`"

/-- `ellipsoid.and`: `Ellipsoid.andPoint` for a point; `empty` is true if certified outside. -/
private def aux_andPoint (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "and" req ["E", "point", "w", "a", "s", "k"]
  let d ← parseEllipsoid dops.readExact (← field req "E")
  let p ← parseVecFixed dops.readExact d.n (← field req "point")
  let r := aux_diff d.E p
  let w ← aux_vecOpt dops req "w" d.n (aux_solve d.E r)
  let a ← aux_vecOpt dops req "a" d.n r
  let s ← match fieldOpt req "s" with
    | some _ => aux_scalar dops req "s"
    | none => pure (sqrtUp (← natField req "k") (d.E.quadUp a))
  match Ellipsoid.andPoint d.E p w a s with
  | .empty => pure [("empty", Json.bool true)]
  | .of E' => pure [("empty", Json.bool false), aux_set dops E']

/-- `ellipsoid.contains`: `Ellipsoid.containsPoint` at the witness `w`; `true` proves it inside. -/
private def aux_contains (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  let op := "contains"
  checkFields op req ["E", "point", "w", "tol"]
  checkTol op req
  let d ← parseEllipsoid dops.readExact (← field req "E")
  let p ← parseVecFixed dops.readExact d.n (← field req "point")
  let w ← aux_vecOpt dops req "w" d.n (aux_solve d.E (aux_diff d.E p))
  pure [("contains", Json.bool (Ellipsoid.containsPoint d.E p w))]

/-- `ellipsoid.ellipsoidNorm`: `Ellipsoid.ellipsoidNormUb`; `null` if `Q w = point` fails. -/
private def aux_ellipsoidNorm (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  let op := "ellipsoidNorm"
  checkFields op req ["E", "point", "w", "k"]
  let d ← parseEllipsoid dops.readExact (← field req "E")
  let p ← parseVecFixed dops.readExact d.n (← field req "point")
  let w ← aux_vecOpt dops req "w" d.n (aux_solve d.E p)
  match Ellipsoid.ellipsoidNormUb (← natField req "k") d.E p w with
  | some v => valueScalar dops.showExact v
  | none => pure [("value", Json.null)]

/-- `ellipsoid.enclosePoints`: `Ellipsoid.enclosePointsCov` for the rotations `T`, `U`. -/
private def aux_enclosePoints (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  let op := "enclosePoints"
  checkFields op req ["points", "T", "U", "k", "method"]
  checkStrOption op req "method" "cov"
  let dm ← parseMatDyn dops.readExact (← field req "points")
  let T ← aux_square dops req "T" dm.r
  let U ← aux_square dops req "U" dm.r
  pure [aux_set dops (Ellipsoid.enclosePointsCov (← natField req "k") (N := dm.c) (n := dm.r)
    (fun l i => dm.M i l) T U)]

/-- `ellipsoid.interval`: `Ellipsoid.interval` at the half-widths `s`. -/
private def aux_interval (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  let op := "interval"
  checkFields op req ["E", "s", "k"]
  let d ← parseEllipsoid dops.readExact (← field req "E")
  let s ← aux_boxS dops req d.E
  pure [("I", printIntervalVec dops.showExact (Ellipsoid.interval d.E s))]

/-- `ellipsoid.isBadDir`: `Ellipsoid.isGoodDir` at the eigenvalue bound `mu`; `good`. -/
private def aux_isBadDir (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  let op := "isBadDir"
  checkFields op req ["E", "E2", "dir", "mu"]
  let d ← parseEllipsoid dops.readExact (← field req "E")
  let e2 ← parseEllipsoidFixed dops.readExact d.n (← field req "E2")
  let l ← parseVecFixed dops.readExact d.n (← field req "dir")
  pure [("good", Json.bool (Ellipsoid.isGoodDir d.E e2 l (← aux_scalar dops req "mu")))]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `ellipsoid.vertices`: the two ends of a one-dimensional ellipsoid, `k` Newton steps. -/
def handleEllipsoidVertices (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "vertices" req ["E", "k"]
  let d ← parseEllipsoid dops.readExact (← field req "E")
  let k ← natField req "k"
  if h : d.n = 1 then
    let vs := Ellipsoid.vertices k (h ▸ d.E)
    let data := (vs.map fun v => Json.str (dops.showExact (v 0))).toArray
    pure [("V", Json.mkObj [("rows", Lean.toJson 1), ("cols", Lean.toJson vs.length),
      ("data", Json.arr data)])]
  else throw s!"vertices: the ellipsoid has dimension {d.n}, CORA's vertices is for one dimension"

/-- Every op of this file, without the `ellipsoid.` prefix. -/
def ellipsoidOpNames : List String :=
  [ "and", "cartProd", "center", "construct", "contains", "ellipsoidNorm", "enclosePoints",
    "interval", "intersectStrip", "isBadDir", "isBigger", "isBounded", "isFullDim", "isequal",
    "lift", "mtimes", "norm", "origin", "project", "radius", "representsa", "vertices",
    "zonotope" ]

/-- `op` of `ellipsoid.`, run; `none` for a name this file does not serve. -/
@[noinline, nospecialize]
def handleEllipsoidOp (dops : DtypeOps 𝕋) (op : String) (req : Json) : Option Resp :=
  match op with
  | "and" => some (aux_andPoint dops req)
  | "cartProd" => some (if (fieldOpt req "E2").isSome then aux_cartProd2 dops req else do
      checkFields op req ["E", "v"]
      let d ← parseEllipsoid dops.readExact (← field req "E")
      let ⟨_, v⟩ ← parseVecDyn dops.readExact (← field req "v")
      pure [aux_set dops (Ellipsoid.cartProdVec d.E v)])
  | "center" => some (do
      checkFields op req ["E"]
      let d ← parseEllipsoid dops.readExact (← field req "E")
      pure [("value", printVec dops.showExact (Ellipsoid.center d.E))])
  -- the arms from `construct` on
  | "construct" => some (do
      checkFields op req ["E"]
      let d ← parseEllipsoid dops.readExact (← field req "E")
      pure [aux_set dops d.E])
  | "contains" => some (aux_contains dops req)
  | "ellipsoidNorm" => some (aux_ellipsoidNorm dops req)
  | "enclosePoints" => some (aux_enclosePoints dops req)
  -- the arms from `interval` on
  | "interval" => some (aux_interval dops req)
  | "intersectStrip" => some (aux_strip dops req)
  | "isBadDir" => some (aux_isBadDir dops req)
  -- the arms from `isBigger` on
  | "isBigger" => some (do
      checkFields op req ["E", "E2"]
      let d ← parseEllipsoid dops.readExact (← field req "E")
      let e2 ← parseEllipsoidFixed dops.readExact d.n (← field req "E2")
      valueBool (Ellipsoid.isBigger d.E e2))
  | "isBounded" => some (do
      checkFields op req ["E", "tol"]
      checkTol op req
      valueBool true)
  | "isFullDim" => some (aux_test op dops req fun E => Ellipsoid.isFullDim E)
  | "isequal" => some (do
      checkFields op req ["E", "E2", "tol"]
      checkTol op req
      let d ← parseEllipsoid dops.readExact (← field req "E")
      let e2 ← parseEllipsoidFixed dops.readExact d.n (← field req "E2")
      valueBool (Ellipsoid.isequal d.E e2))
  -- the arms from `lift` on
  | "lift" => some (do
      checkFields op req ["E", "N", "dims"]
      let d ← parseEllipsoid dops.readExact (← field req "E")
      let e ← liftPerm req d.n
      pure [aux_set dops (Ellipsoid.reindex e.symm d.E)])
  | "mtimes" => some (do
      checkFields op req ["E", "M"]
      let d ← parseEllipsoid dops.readExact (← field req "E")
      let ⟨_, M⟩ ← parseMatColsFixed dops.readExact d.n (← field req "M")
      pure [aux_set dops (Ellipsoid.mtimes M d.E)])
  -- the arms from `norm` on
  | "norm" => some (do
      checkFields op req ["E", "k", "type"]
      match fieldOpt req "type" with
      | none => pure ()
      | some j =>
        unless j.getNat?.toOption = some 2 || j.getStr?.toOption = some "2" do
          throw "norm: `type` must be 2, the float definition is the Euclidean norm"
      let d ← parseEllipsoid dops.readExact (← field req "E")
      valueScalar dops.showExact (Ellipsoid.normUb (← natField req "k") d.E))
  | "origin" => some (do
      checkFields op req ["n"]
      pure [aux_set dops (Ellipsoid.origin (𝕋 := 𝕋) (← natField req "n"))])
  -- the arms from `project` on
  | "project" => some (do
      checkFields op req ["E", "dims"]
      let d ← parseEllipsoid dops.readExact (← field req "E")
      let ⟨_, dims⟩ ← indexArrField req "dims" d.n
      pure [aux_set dops (Ellipsoid.project d.E dims)])
  | "radius" => some (do
      checkFields op req ["E", "p"]
      let d ← parseEllipsoid dops.readExact (← field req "E")
      valueScalar dops.showExact (Ellipsoid.radius (← natField req "p") d.E))
  | "representsa" => some (do
      checkFields op req ["E", "type", "tol"]
      checkTol op req
      let d ← parseEllipsoid dops.readExact (← field req "E")
      match ← strField req "type" with
      | "point" => valueBool (Ellipsoid.representsa_point d.E)
      | "origin" => valueBool (Ellipsoid.representsa_origin d.E)
      | t => throw s!"representsa: `type` must be point or origin, not `{t}`")
  -- the arms from `vertices` on
  | "vertices" => some (handleEllipsoidVertices dops req)
  | "zonotope" => some (do
      checkFields op req ["E"]
      let d ← parseEllipsoid dops.readExact (← field req "E")
      pure [("Z", printZonotope dops.showExact (Ellipsoid.zonotope d.E))])
  | _ => none

end CORALean.Oracle


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
