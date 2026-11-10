import CORALean.ContSet.ConZonotope.Float.Instances
import CORALean.ContSet.ConZonotope.Float.Operations.CartProd
import CORALean.ContSet.ConZonotope.Float.Operations.Compact
import CORALean.ContSet.ConZonotope.Float.Operations.FourierMotzkinIter
import CORALean.ContSet.ConZonotope.Float.Operations.ConIntersect
import CORALean.ContSet.ConZonotope.Float.Operations.CubMap
import CORALean.ContSet.ConZonotope.Float.Operations.Empty
import CORALean.ContSet.ConZonotope.Float.Operations.IntersectStrip
import CORALean.ContSet.ConZonotope.Float.Operations.ContainsPoint
import CORALean.ContSet.ConZonotope.Float.Operations.Intersection
import CORALean.ContSet.ConZonotope.Float.Operations.IsFullDim
import CORALean.ContSet.ConZonotope.Float.Operations.IsDisjointLP
import CORALean.ContSet.ConZonotope.Float.Operations.Isequal
import CORALean.ContSet.ConZonotope.Float.Operations.LinComb
import CORALean.ContSet.ConZonotope.Float.Operations.Mtimes
import CORALean.ContSet.ConZonotope.Float.Operations.Origin
import CORALean.ContSet.ConZonotope.Float.Operations.Plus
import CORALean.ContSet.ConZonotope.Float.Operations.Project
import CORALean.ContSet.ConZonotope.Float.Operations.QuadMap
import CORALean.ContSet.ConZonotope.Float.Operations.Reduce
import CORALean.ContSet.ConZonotope.Float.Operations.Reindex
import CORALean.ContSet.ConZonotope.Float.Operations.RepresentsaEmptySet
import CORALean.ContSet.ConZonotope.Float.Operations.Split
import CORALean.ContSet.ConZonotope.Float.Operations.SupportBound
import CORALean.ContSet.Conversion.Float.Operations.Basic
import CORALean.ContSet.Conversion.Float.Operations.ConZonotope_to_IntervalTight
import CORALean.ContSet.ContSet.Operations.Enclose
import CORALean.ContSet.Zonotope.Float.Operations.RightInvCandidate
import CORALean.Examples.Oracle.Ops.SetCodec
import CORALean.Specification.Instances

/-!
# The constrained-zonotope ops: CORA's `conZonotope` methods

Thin adapters over the float definitions `references/coverage/contSet/conZonotope.md` links.
Operands are `cZ`, `cZ2` (`{"c","G","P","E"}`, or `{"c","G","A","b","E"}` with `A ξ = b`; see
`SetCodec.lean`); a set result is `cZ` (`cZ1`, `cZ2` for a split), a Boolean `value`, a bound
`value`. Indices are 0-based; a field an op does not list is refused by name. `contains` (a point)
and `isFullDim` take the certificate as the optional fields `H` (default
`Zonotope.rightInvCandidate`) and `beta0` (default `0`), and answer `false` for an equality row
`A ξ = b`. Not served: `minkDiff`, `rescale`, `polytope`, the constructor (README).

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

private def aux_set (dops : DtypeOps 𝕋) (name : String) {n : Nat} (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) :
    String × Json :=
  (name, printConZonotope dops.showExact cZ)

/-- Two constrained zonotopes of one dimension in. -/
private def aux_pair (dops : DtypeOps 𝕋) (req : Json) :
    Except String (Σ n : Nat, ConZonotope 𝕋 (Vec 𝕋 n) × ConZonotope 𝕋 (Vec 𝕋 n)) := do
  let d ← parseConZonotope dops.readExact (← field req "cZ")
  let c2 ← parseConZonotopeFixed dops.readExact d.n (← field req "cZ2")
  pure ⟨d.n, d.cZ, c2⟩

private def aux_unary (op : String) (dops : DtypeOps 𝕋) (req : Json) (extra : List String)
    (f : {n : Nat} → ConZonotope 𝕋 (Vec 𝕋 n) → ConZonotope 𝕋 (Vec 𝕋 n)) : Resp := do
  checkFields op req ("cZ" :: extra)
  let d ← parseConZonotope dops.readExact (← field req "cZ")
  pure [aux_set dops "cZ" (f d.cZ)]

private def aux_binary (op : String) (dops : DtypeOps 𝕋) (req : Json)
    (f : {n : Nat} → ConZonotope 𝕋 (Vec 𝕋 n) → ConZonotope 𝕋 (Vec 𝕋 n) →
      ConZonotope 𝕋 (Vec 𝕋 n)) : Resp := do
  checkFields op req ["cZ", "cZ2"]
  let ⟨_, a, b⟩ ← aux_pair dops req
  pure [aux_set dops "cZ" (f a b)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `conZonotope.conIntersect`: `cZ ∩_M cZ2`, `M` the `m × n` map into the second set's space. -/
def handleConZonoConIntersect (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "conIntersect" req ["cZ", "cZ2", "R"]
  let d ← parseConZonotope dops.readExact (← field req "cZ")
  let d2 ← parseConZonotope dops.readExact (← field req "cZ2")
  let ⟨r, M⟩ ← parseMatColsFixed dops.readExact d.n (← field req "R")
  if h : r = d2.n then
    pure [aux_set dops "cZ" (ConZonotope.conIntersect d.cZ d2.cZ (h ▸ M))]
  else throw s!"conIntersect: `R` has {r} rows, the second set has dimension {d2.n}"

/-- `conZonotope.cartProd`. -/
def handleConZonoCartProd (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "cartProd" req ["cZ", "cZ2"]
  let a ← parseConZonotope dops.readExact (← field req "cZ")
  let b ← parseConZonotope dops.readExact (← field req "cZ2")
  pure [aux_set dops "cZ" (ConZonotope.cartProd a.cZ b.cZ)]

/-- `conZonotope.mtimes`: `M cZ`, `M` a matrix. -/
def handleConZonoMtimes (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "mtimes" req ["cZ", "M"]
  let d ← parseConZonotope dops.readExact (← field req "cZ")
  let ⟨_, M⟩ ← parseMatColsFixed dops.readExact d.n (← field req "M")
  pure [aux_set dops "cZ" (ConZonotope.mtimes M d.cZ)]

/-- `conZonotope.quadMap`: `Q` an array of `n × n` matrices. -/
def handleConZonoQuadMap (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "quadMap" req ["cZ", "Q"]
  let d ← parseConZonotope dops.readExact (← field req "cZ")
  let ⟨_, Q⟩ ← parseSquareList dops.readExact d.n (← field req "Q")
  pure [aux_set dops "cZ" (ConZonotope.quadMap Q d.cZ)]

/-- `conZonotope.cubMap`: `T` an array of arrays of `n × n` matrices. -/
def handleConZonoCubMap (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "cubMap" req ["cZ", "T"]
  let d ← parseConZonotope dops.readExact (← field req "cZ")
  let ⟨_, T⟩ ← parseTensor dops.readExact d.n (← field req "T")
  pure [aux_set dops "cZ" (ConZonotope.cubMap T d.cZ)]

/-- `conZonotope.intersectStrip`: the strips `|C x - y| ≤ phi` at the gain `Lambda`. -/
def handleConZonoIntersectStrip (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "intersectStrip" req ["cZ", "C", "phi", "y", "Lambda"]
  let d ← parseConZonotope dops.readExact (← field req "cZ")
  let ⟨s, C⟩ ← parseMatColsFixed dops.readExact d.n (← field req "C")
  let φ ← parseVecFixed dops.readExact s (← field req "phi")
  let y ← parseVecFixed dops.readExact s (← field req "y")
  let ⟨r, Λ⟩ ← parseMatColsFixed dops.readExact s (← field req "Lambda")
  if h : r = d.n then
    pure [aux_set dops "cZ" (ConZonotope.intersectStrip d.cZ C φ y (h ▸ Λ))]
  else throw s!"intersectStrip: `Lambda` has {r} rows, expected {d.n}"

/-- `conZonotope.supportFunc`: the upper bound of `dir · x`, `ConZonotope.boundDot`. -/
def handleConZonoSupportFunc (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "supportFunc" req ["cZ", "dir", "type"]
  checkStrOption "supportFunc" req "type" "upper"
  let d ← parseConZonotope dops.readExact (← field req "cZ")
  let a ← parseVecFixed dops.readExact d.n (← field req "dir")
  valueScalar dops.showExact (d.cZ.boundDot (c := rowFunctional a) a fun _ => rfl).val

/-- `conZonotope.reduce`: `order` the target order, `method` `girard`. -/
def handleConZonoReduce (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "reduce" req ["cZ", "order", "method"]
  checkStrOption "reduce" req "method" "girard"
  let d ← parseConZonotope dops.readExact (← field req "cZ")
  pure [aux_set dops "cZ" (ConZonotope.reduce d.cZ (← natField req "order"))]

/-- `conZonotope.split`: halves along coordinate `dim`. -/
def handleConZonoSplit (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "split" req ["cZ", "dim"]
  let d ← parseConZonotope dops.readExact (← field req "cZ")
  let j ← indexField req "dim" d.n
  let (a, b) := ConZonotope.split d.cZ j
  pure [aux_set dops "cZ1" a, aux_set dops "cZ2" b]

/-- `conZonotope.enclose`: CORA's `enclose(cZ, M, cZ2)`, `ContSet.enclose` at the float
instances. -/
def handleConZonoEnclose (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "enclose" req ["cZ", "M", "cZ2"]
  let d ← parseConZonotope dops.readExact (← field req "cZ")
  let c2 ← parseConZonotopeFixed dops.readExact d.n (← field req "cZ2")
  let ⟨r, M⟩ ← parseMatColsFixed dops.readExact d.n (← field req "M")
  if h : r = d.n then
    pure [aux_set dops "cZ" (ContSet.enclose (𝕋 := 𝕋) (S := fun k => ConZonotope 𝕋 (Vec 𝕋 k)) d.cZ
      (h ▸ M) c2)]
  else throw s!"enclose: `M` has {r} rows, expected {d.n}"

/-- `conZonotope.vertices`: the corners of the bounding box, `ConZonotope.vPolytopeBox`. -/
def handleConZonoVertices (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "vertices" req ["cZ"]
  let d ← parseConZonotope dops.readExact (← field req "cZ")
  let P := ConZonotope.vPolytopeBox d.cZ
  pure [("V", printMat dops.showExact (fun (i : Fin d.n) (l : Fin P.k) => P.V l i)),
    ("E", printIntervalVec dops.showExact P.I_error)]

/-- The certificate of `contains` and `isFullDim`: `H`, a right inverse of `G` (default
`Zonotope.rightInvCandidate`), and `beta0`, a coefficient point (default `0`). -/
private def aux_certificate (dops : DtypeOps 𝕋) (req : Json) {n : Nat}
    (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) : Except String (Mat 𝕋 cZ.h n × Vec 𝕋 cZ.h) := do
  let H ← match fieldOpt req "H" with
    | none =>
      let tab := tableOf (Zonotope.rightInvCandidate fun (i : Fin n) (l : Fin cZ.h) => cZ.G l i)
      pure fun j i => tableGet FloatOps.zero tab j i
    | some hj =>
      let ⟨r, Hm⟩ ← parseMatColsFixed dops.readExact n hj
      if h : r = cZ.h then pure (h ▸ Hm)
      else throw s!"`H` has {r} rows, the constrained zonotope has {cZ.h} generators"
  let β ← match fieldOpt req "beta0" with
    | none => pure (fun (_ : Fin cZ.h) => (FloatOps.zero : 𝕋))
    | some bj => parseVecFixed dops.readExact cZ.h bj
  pure (H, β)

/-- `conZonotope.isFullDim`: `ConZonotope.isFullDim` at the certificate; `true` proves an interior
point. -/
def handleConZonoIsFullDim (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "isFullDim" req ["cZ", "tol", "H", "beta0"]
  checkTol "isFullDim" req
  let d ← parseConZonotope dops.readExact (← field req "cZ")
  let (H, β) ← aux_certificate dops req d.cZ
  valueBool (ConZonotope.isFullDim d.cZ H β)

/-- `conZonotope.contains`: `ConZonotope.containsPoint` for the column `point`; `true` proves the
point inside. A zonotope or a box as the second operand has no float definition. -/
def handleConZonoContains (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "contains" req ["cZ", "point", "tol", "H", "beta0"]
  checkTol "contains" req
  let d ← parseConZonotope dops.readExact (← field req "cZ")
  let p ← parseVecFixed dops.readExact d.n (← field req "point")
  let (H, β) ← aux_certificate dops req d.cZ
  pure [("contains", Json.bool (ConZonotope.containsPoint d.cZ H β p))]

/-- `conZonotope.fourierMotzkinBounds`: one pass on `C x <= d` from the box `B`, or `k` passes
from the unit box. The first step of CORA's `approximateBoundsWithGPU`; `I`. -/
def handleConZonoFourierMotzkin (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "fourierMotzkinBounds" req ["C", "d", "B", "k"]
  let dm ← parseMatDyn dops.readExact (← field req "C")
  let d ← parseVecFixed dops.readExact dm.r (← field req "d")
  let I ← match fieldOpt req "B", fieldOpt req "k" with
    | some bj, none =>
      let B ← parseIntervalVecFixed dops.readExact dm.c bj
      pure (ConZonotope.fourierMotzkinBounds dm.M d B)
    | none, some _ => pure (ConZonotope.fourierMotzkinIter dm.M d (← natField req "k"))
    | _, _ => throw "fourierMotzkinBounds: give exactly one of `B` (one pass) and `k` (passes)"
  pure [("I", printIntervalVec dops.showExact I)]

/-- `conZonotope.intervalTight`: `ConZonotope.intervalTight`, the box of `c + G beta + E` with the
factors bounded by `k` Fourier-Motzkin passes on the constraint; `I`. CORA's `interval` bounds
them by linear programs. -/
def handleConZonoIntervalTight (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "intervalTight" req ["cZ", "k"]
  let d ← parseConZonotope dops.readExact (← field req "cZ")
  pure [("I", printIntervalVec dops.showExact
    (ConZonotope.intervalTight (← natField req "k") d.cZ))]

/-- Every op of this file, without the `conZonotope.` prefix. -/
def conZonotopeOpNames : List String :=
  [ "and", "cartProd", "compact", "conIntersect", "contains", "convHull", "cubMap", "empty",
    "enclose", "fourierMotzkinBounds", "intersectStrip", "isBounded", "isFullDim", "isIntersecting",
    "isequal", "lift", "mtimes", "origin", "plus", "project", "quadMap", "reduce", "representsa",
    "split", "supportFunc", "vertices", "zonotope", "interval", "intervalTight",
    "zonoBundle" ]

/-- `op` of `conZonotope.`, run; `none` for a name this file does not serve. -/
@[noinline, nospecialize]
def handleConZonotopeOp (dops : DtypeOps 𝕋) (op : String) (req : Json) : Option Resp :=
  match op with
  | "and" => some (aux_binary op dops req fun a b => ConZonotope.intersection a b)
  | "cartProd" => some (handleConZonoCartProd dops req)
  | "compact" => some (do
      checkStrOption op req "method" "zeros"
      checkTol op req
      aux_unary op dops req ["method", "tol"] fun cZ => ConZonotope.compact cZ)
  | "conIntersect" => some (handleConZonoConIntersect dops req)
  | "contains" => some (handleConZonoContains dops req)
  | "convHull" => some (aux_binary op dops req fun a b => ConZonotope.linComb a b)
  -- the arms from `cubMap` on
  | "cubMap" => some (handleConZonoCubMap dops req)
  | "empty" => some (do
      checkFields op req ["n"]
      pure [aux_set dops "cZ" (ConZonotope.empty (𝕋 := 𝕋) (← natField req "n"))])
  | "enclose" => some (handleConZonoEnclose dops req)
  | "fourierMotzkinBounds" => some (handleConZonoFourierMotzkin dops req)
  | "intersectStrip" => some (handleConZonoIntersectStrip dops req)
  | "isBounded" => some (do
      checkFields op req ["cZ", "tol"]
      checkTol op req
      valueBool true)
  | "isFullDim" => some (handleConZonoIsFullDim dops req)
  -- the arms from `isIntersecting` on
  | "isIntersecting" => some (do
      checkFields op req ["cZ", "cZ2", "tol", "type"]
      checkTol op req
      let ⟨_, a, b⟩ ← aux_pair dops req
      pure [("disjoint", Json.bool (ConZonotope.isDisjointLP a b))])
  | "isequal" => some (do
      checkFields op req ["cZ", "cZ2", "tol"]
      checkTol op req
      let ⟨_, a, b⟩ ← aux_pair dops req
      valueBool (ConZonotope.isequal a b))
  -- the arms from `lift` on
  | "lift" => some (do
      checkFields op req ["cZ", "N", "dims"]
      let d ← parseConZonotope dops.readExact (← field req "cZ")
      let e ← liftPerm req d.n
      pure [aux_set dops "cZ" (ConZonotope.reindex e.symm d.cZ)])
  | "mtimes" => some (handleConZonoMtimes dops req)
  | "origin" => some (do
      checkFields op req ["n"]
      pure [aux_set dops "cZ" (ConZonotope.origin (𝕋 := 𝕋) (← natField req "n"))])
  | "plus" => some (aux_binary op dops req fun a b => ConZonotope.plus a b)
  -- the arms from `project` on
  | "project" => some (do
      checkFields op req ["cZ", "dims"]
      let d ← parseConZonotope dops.readExact (← field req "cZ")
      let ⟨_, dims⟩ ← indexArrField req "dims" d.n
      pure [aux_set dops "cZ" (ConZonotope.project d.cZ dims)])
  | "quadMap" => some (handleConZonoQuadMap dops req)
  | "reduce" => some (handleConZonoReduce dops req)
  | "representsa" => some (do
      checkFields op req ["cZ", "type", "tol"]
      checkTol op req
      checkStrOption op req "type" "emptySet"
      let d ← parseConZonotope dops.readExact (← field req "cZ")
      valueBool (ConZonotope.representsa_emptySet d.cZ))
  -- the arms from `split` on
  | "split" => some (handleConZonoSplit dops req)
  | "intervalTight" => some (handleConZonoIntervalTight dops req)
  | "supportFunc" => some (handleConZonoSupportFunc dops req)
  | "vertices" => some (handleConZonoVertices dops req)
  -- the conversions: drop the constraints, the bounding box, a bundle of one
  | "zonotope" | "interval" | "zonoBundle" => some (do
      checkFields op req ["cZ"]
      let d ← parseConZonotope dops.readExact (← field req "cZ")
      match op with
      | "zonotope" => pure [("Z", printZonotope dops.showExact (ConZonotope.zonotope d.cZ))]
      | "interval" => pure [("I", printIntervalVec dops.showExact (ConZonotope.interval d.cZ))]
      | _ => pure [("zB", printZonoBundle dops.showExact (ConZonotope.zonoBundle d.cZ))])
  | _ => none

end CORALean.Oracle


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
