import CORALean.ContSet.Capsule.Float.Operations.BoundDotUp
import CORALean.ContSet.Capsule.Float.Operations.ContainsPoint
import CORALean.ContSet.Capsule.Float.Operations.ConvHull
import CORALean.ContSet.Capsule.Float.Operations.Enclose
import CORALean.ContSet.Capsule.Float.Operations.EnclosePoints
import CORALean.ContSet.Capsule.Float.Operations.IsDisjoint
import CORALean.ContSet.Capsule.Float.Operations.IsFullDim
import CORALean.ContSet.Capsule.Float.Operations.Isequal
import CORALean.ContSet.Capsule.Float.Operations.Mtimes
import CORALean.ContSet.Capsule.Float.Operations.Plus
import CORALean.ContSet.Capsule.Float.Operations.Project
import CORALean.ContSet.Capsule.Float.Operations.Reduce
import CORALean.ContSet.Capsule.Float.Operations.Reindex
import CORALean.ContSet.Capsule.Float.Operations.Vertices
import CORALean.ContSet.Capsule.Float.Operations.Volume
import CORALean.ContSet.Conversion.Float.Operations.Basic
import CORALean.ContSet.Conversion.Float.Operations.Capsule_to_HPolytope
import CORALean.ContSet.Conversion.Float.Operations.Capsule_to_Zonotope
import CORALean.Examples.Oracle.Ops.SetCodec

/-!
# The capsule ops: CORA's `capsule` methods

Thin adapters over the float definitions `references/coverage/contSet/capsule.md` links. Operands
are `C`, `C2` (`{"c","g","r","E"}`, see `SetCodec.lean`); a set result is `C`, a box `I`, a
zonotope `Z`, a halfspace polytope `P`, an ellipsoid `E`, a Boolean, a vector or a bound `value`.
`k` (Newton steps of the roots) and `p` (steps of the trigonometric enclosures) are the tuning
the float definitions take, which CORA has no argument for, so they are required where listed.
Indices are 0-based; a field an op does not list is refused by name. Not served: the classes
without a wire format (`conPolyZono`, `spectraShadow`) and the constructor `capsule`.

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

private def aux_set (dops : DtypeOps 𝕋) {n : Nat} (C : Capsule 𝕋 n) : String × Json :=
  ("C", printCapsule dops.showExact C)

/-- Two capsules of one dimension in. -/
private def aux_pair (dops : DtypeOps 𝕋) (req : Json) :
    Except String (Σ n : Nat, Capsule 𝕋 n × Capsule 𝕋 n) := do
  let d ← parseCapsule dops.readExact (← field req "C")
  let c2 ← parseCapsuleFixed dops.readExact d.n (← field req "C2")
  pure ⟨d.n, d.C, c2⟩


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `capsule.vertices`: the boxes around the sampled boundary points, `Capsule.vertices p k`. -/
def handleCapsuleVertices (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "vertices" req ["C", "p", "k"]
  let d ← parseCapsule dops.readExact (← field req "C")
  if h : d.n = 2 then
    let bs := Capsule.vertices (← natField req "p") (← natField req "k") (h ▸ d.C)
    pure [("boxes", Json.arr (bs.toArray.map (printIntervalVec dops.showExact)))]
  else throw s!"vertices: the capsule has dimension {d.n}, CORA's vertices is planar"

/-- `capsule.enclose`: CORA's `enclose(C, M, C2)` at `k` Newton steps. -/
def handleCapsuleEnclose (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "enclose" req ["C", "M", "C2", "k"]
  let d ← parseCapsule dops.readExact (← field req "C")
  let ⟨m, M⟩ ← parseMatRowsFixed dops.readExact d.n (← field req "M")
  let c2 ← parseCapsuleFixed dops.readExact m (← field req "C2")
  pure [aux_set dops (Capsule.enclose (← natField req "k") d.C M c2)]

/-- Every op of this file, without the `capsule.` prefix. -/
def capsuleOpNames : List String :=
  [ "center", "contains", "convHull", "empty", "enclose", "enclosePoints", "ellipsoid",
    "interval", "isBounded", "isFullDim", "isIntersecting", "isequal", "lift", "mtimes", "origin",
    "plus", "polytope", "project", "radius", "reduce", "representsa", "supportFunc", "vertices",
    "volume", "zonotope" ]

/-- `op` of `capsule.`, run; `none` for a name this file does not serve. -/
@[noinline, nospecialize]
def handleCapsuleOp (dops : DtypeOps 𝕋) (op : String) (req : Json) : Option Resp :=
  match op with
  | "center" => some (do
      checkFields op req ["C"]
      let d ← parseCapsule dops.readExact (← field req "C")
      pure [("value", printVec dops.showExact (Capsule.center d.C))])
  | "contains" => some (do
      checkFields op req ["C", "point", "tol", "type"]
      checkTol op req
      let d ← parseCapsule dops.readExact (← field req "C")
      let p ← parseVecFixed dops.readExact d.n (← field req "point")
      pure [("contains", Json.bool (Capsule.containsPoint d.C p))])
  -- the arms from `convHull` on
  | "convHull" => some (do
      checkFields op req ["C", "C2", "k"]
      let ⟨_, a, b⟩ ← aux_pair dops req
      pure [aux_set dops (Capsule.convHull (← natField req "k") a b)])
  | "empty" => some (do
      checkFields op req ["n"]
      pure [aux_set dops (Capsule.empty (𝕋 := 𝕋) (← natField req "n"))])
  | "enclose" => some (handleCapsuleEnclose dops req)
  | "enclosePoints" => some (do
      checkFields op req ["points", "k"]
      let dm ← parseMatDyn dops.readExact (← field req "points")
      pure [aux_set dops (Capsule.enclosePoints (← natField req "k") (N := dm.c) (n := dm.r)
        (fun l i => dm.M i l))])
  -- the arms from `ellipsoid` on
  | "ellipsoid" => some (do
      checkFields op req ["C", "sigma"]
      let d ← parseCapsule dops.readExact (← field req "C")
      let σ ← match dops.readExact "sigma" (← scalarField req "sigma") with
        | .ok v => pure v
        | .error e => throw e
      pure [("E", printEllipsoid dops.showExact (Capsule.ellipsoid d.C σ))])
  | "interval" => some (do
      checkFields op req ["C"]
      let d ← parseCapsule dops.readExact (← field req "C")
      pure [("I", printIntervalVec dops.showExact (Capsule.interval d.C))])
  -- the arms from `isBounded` on
  | "isBounded" => some (do
      checkFields op req ["C", "tol"]
      checkTol op req
      valueBool true)
  | "isFullDim" => some (do
      checkFields op req ["C", "tol"]
      checkTol op req
      let d ← parseCapsule dops.readExact (← field req "C")
      valueBool (Capsule.isFullDim d.C))
  | "isIntersecting" => some (do
      checkFields op req ["C", "C2", "k", "tol", "type"]
      checkTol op req
      let ⟨_, a, b⟩ ← aux_pair dops req
      pure [("disjoint", Json.bool (Capsule.isDisjoint (← natField req "k") a b))])
  -- the arms from `isequal` on
  | "isequal" => some (do
      checkFields op req ["C", "C2", "tol"]
      checkTol op req
      let ⟨_, a, b⟩ ← aux_pair dops req
      valueBool (Capsule.isequal a b))
  | "lift" => some (do
      checkFields op req ["C", "N", "dims"]
      let d ← parseCapsule dops.readExact (← field req "C")
      let e ← liftPerm req d.n
      pure [aux_set dops (Capsule.reindex e.symm d.C)])
  -- the arms from `mtimes` on
  | "mtimes" => some (do
      checkFields op req ["C", "M", "k"]
      let d ← parseCapsule dops.readExact (← field req "C")
      let ⟨_, M⟩ ← parseMatColsFixed dops.readExact d.n (← field req "M")
      pure [aux_set dops (Capsule.mtimes (← natField req "k") M d.C)])
  | "origin" => some (do
      checkFields op req ["n"]
      pure [aux_set dops (Capsule.origin (𝕋 := 𝕋) (← natField req "n"))])
  | "plus" => some (do
      checkFields op req ["C", "C2", "k"]
      let ⟨_, a, b⟩ ← aux_pair dops req
      pure [aux_set dops (Capsule.plus (← natField req "k") a b)])
  -- the arms from `polytope` on
  | "polytope" => some (do
      checkFields op req ["C", "p"]
      let d ← parseCapsule dops.readExact (← field req "C")
      pure [("P", printHPolytope dops.showExact (Capsule.hPolytope (← natField req "p") d.C))])
  | "project" => some (do
      checkFields op req ["C", "dims"]
      let d ← parseCapsule dops.readExact (← field req "C")
      let ⟨_, dims⟩ ← indexArrField req "dims" d.n
      pure [aux_set dops (Capsule.project d.C dims)])
  | "radius" => some (do
      checkFields op req ["C", "k"]
      let d ← parseCapsule dops.readExact (← field req "C")
      valueScalar dops.showExact (Capsule.radius (← natField req "k") d.C))
  -- the arms from `reduce` on
  | "reduce" => some (do
      checkFields op req ["C", "order", "method"]
      let d ← parseCapsule dops.readExact (← field req "C")
      pure [aux_set dops (Capsule.reduce d.C (← natField req "order"))])
  | "representsa" => some (do
      checkFields op req ["C", "type", "tol"]
      checkTol op req
      let d ← parseCapsule dops.readExact (← field req "C")
      match ← strField req "type" with
      | "point" => valueBool (Capsule.representsa_point d.C)
      | "origin" => valueBool (Capsule.representsa_origin d.C)
      | t => throw s!"representsa: `type` must be point or origin, not `{t}`")
  -- the arms from `supportFunc` on
  | "supportFunc" => some (do
      checkFields op req ["C", "dir", "type", "p"]
      checkStrOption op req "type" "upper"
      let d ← parseCapsule dops.readExact (← field req "C")
      let a ← parseVecFixed dops.readExact d.n (← field req "dir")
      valueScalar dops.showExact
        (d.C.boundDotUp (f := rowFunctional a) a (fun _ => rfl) (← natField req "p")).val)
  | "vertices" => some (handleCapsuleVertices dops req)
  | "volume" => some (do
      checkFields op req ["C", "p", "k"]
      let d ← parseCapsule dops.readExact (← field req "C")
      valueScalar dops.showExact (Capsule.volume (← natField req "p") (← natField req "k") d.C))
  -- the arms from `zonotope` on
  | "zonotope" => some (do
      checkFields op req ["C"]
      let d ← parseCapsule dops.readExact (← field req "C")
      pure [("Z", printZonotope dops.showExact (Capsule.zonotope d.C))])
  | _ => none

end CORALean.Oracle


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
