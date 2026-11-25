import CORALean.ContSet.ConPolyZono.Float.Instances
import CORALean.ContSet.ConPolyZono.Float.Operations.Basic
import CORALean.ContSet.ConPolyZono.Float.Operations.CartProd
import CORALean.ContSet.ConPolyZono.Float.Operations.Compact
import CORALean.ContSet.ConPolyZono.Float.Operations.ConvHull
import CORALean.ContSet.ConPolyZono.Float.Operations.Empty
import CORALean.ContSet.ConPolyZono.Float.Operations.ExactPlus
import CORALean.ContSet.ConPolyZono.Float.Operations.GetSubset
import CORALean.ContSet.ConPolyZono.Float.Operations.Intersection
import CORALean.ContSet.ConPolyZono.Float.Operations.Isequal
import CORALean.ContSet.ConPolyZono.Float.Operations.LinComb
import CORALean.ContSet.ConPolyZono.Float.Operations.Materialise
import CORALean.ContSet.ConPolyZono.Float.Operations.Mtimes
import CORALean.ContSet.ConPolyZono.Float.Operations.Origin
import CORALean.ContSet.ConPolyZono.Float.Operations.Plus
import CORALean.ContSet.ConPolyZono.Float.Operations.Project
import CORALean.ContSet.ConPolyZono.Float.Operations.Reduce
import CORALean.ContSet.ConPolyZono.Float.Operations.Reindex
import CORALean.ContSet.ConPolyZono.Float.Operations.RepresentsaPoint
import CORALean.ContSet.ConPolyZono.Float.Operations.SplitDepFactor
import CORALean.ContSet.ConPolyZono.Float.Operations.SplitLongestGen
import CORALean.ContSet.ConPolyZono.Float.Operations.SplitWith
import CORALean.ContSet.Conversion.Float.Operations.Basic
import CORALean.ContSet.Conversion.Float.Operations.ConPolyZono_to_PolyZonotope
import CORALean.ContSet.Conversion.Float.Operations.ConZonotope_to_ConPolyZono
import CORALean.ContSet.Conversion.Float.Operations.PolyZonotope_to_ConPolyZono
import CORALean.ContSet.Conversion.Float.Operations.PolyZonotope_to_Zonotope
import CORALean.Examples.Oracle.Ops.PolyZonotopeCodec
import CORALean.Examples.Oracle.Ops.SetCodec

/-!
# The constrained-polynomial-zonotope ops: CORA's `conPolyZono` methods

Thin adapters over the float definitions `references/coverage/contSet/conPolyZono.md` links. A set
is `{"c","G","GI","Exp","E","A","b","EC","b_error","id"}`: the polynomial part as a polynomial
zonotope (`PolyZonotopeCodec.lean`), the rows `A μ_EC(α) = b` on the unit box with their slack
`b_error` (none where `A` is absent), the error box `E`. Identifiers (`id`, else `1..p`) only name
the factor of `splitDepFactor` and `getSubset` (`factor`); a result carries none. Operands `cPZ`,
`cPZ2`; a set result `cPZ` (`cPZ1`, `cPZ2` for two halves). `split` is `ConPolyZono.splitWith` at
the box `I` (default `ConPolyZono.interval`). The ops and their fields: the oracle's README.

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

/-- A constrained polynomial zonotope of the dimension read off the request, with the identifiers
of its factors. -/
private structure DynConPolyZono (𝕋 : Type) [FloatOps 𝕋] where
  n : Nat
  cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)
  id : Array Nat

/-- An exponent matrix of `p` rows and `q` columns, `{"rows","cols","data"}` row by row. -/
private def aux_parseExp (p q : Nat) (j : Json) : Except String (Fin p → Fin q → ℕ) := do
  let r ← natField j "rows"
  let c ← natField j "cols"
  if r ≠ p ∨ c ≠ q then throw s!"`EC` is {r}×{c}, expected {p}×{q}"
  let vals ← (← arrField j "data").mapM fun d => match d.getNat? with
    | .ok k => pure k
    | .error _ => throw "`EC` entries must be nonnegative integers"
  if vals.size ≠ p * q then throw s!"`EC` has {vals.size} entries, expected {p * q}"
  pure fun k l => vals.getD (k.val * q + l.val) 0

/-- The constraint rows of the wire set: none where `A` is absent. -/
private def aux_parseCons (dops : DtypeOps 𝕋) (p : Nat) (j : Json) :
    Except String (PolyLevelSet 𝕋 p) := do
  match fieldOpt j "A" with
  | none => pure ⟨0, 0, fun i => i.elim0, fun _ l => l.elim0, fun i => i.elim0, fun i => i.elim0,
      fun _ => .eq, Interval.unit p⟩
  | some aj =>
    let dm ← parseMatDyn dops.readExact aj
    let b ← parseVecFixed dops.readExact dm.r (← field j "b")
    let be ← match fieldOpt j "b_error" with
      | some v => parseVecFixed dops.readExact dm.r v
      | none => pure fun _ => FloatOps.zero
    let R ← aux_parseExp p dm.c (← field j "EC")
    pure ⟨dm.r, dm.c, dm.M, R, b, be, fun _ => .eq, Interval.unit p⟩

/-- A constrained polynomial zonotope of the already-known dimension `n`, with its identifiers. -/
private def aux_parseFixed (dops : DtypeOps 𝕋) (n : Nat) (j : Json) :
    Except String (ConPolyZono 𝕋 (Vec 𝕋 n) × Array Nat) := do
  let pZ ← parsePolyZonotopeFixed dops.readExact n j
  let cons ← aux_parseCons dops pZ.p j
  let cPZ : ConPolyZono 𝕋 (Vec 𝕋 n) :=
    { p := pZ.p, h := pZ.h, qI := pZ.q, c := pZ.c, G := pZ.G, E := pZ.E, GI := pZ.GI,
      cons := { cons with op := fun _ => .eq, dom := Interval.unit pZ.p }, cons_eq := fun _ => rfl,
      cons_dom := rfl, I_error := pZ.I_error }
  pure (cPZ, ← parsePolyZonotopeIds pZ j)

/-- A constrained polynomial zonotope, `n` read off `c`. -/
private def aux_parse (dops : DtypeOps 𝕋) (j : Json) : Except String (DynConPolyZono 𝕋) := do
  let ⟨n, _⟩ ← parseVecDyn dops.readExact (← field j "c")
  let (cPZ, id) ← aux_parseFixed dops n j
  pure ⟨n, cPZ, id⟩

/-- `cPZ` as the wire constrained polynomial zonotope, without identifiers. -/
private def aux_print (dops : DtypeOps 𝕋) {n : Nat} (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) : Json :=
  let P := cPZ.cons
  (printPolyZonotope dops.showExact cPZ.toPolyZonotope).mergeObj (Json.mkObj
    [ ("A", printMat dops.showExact P.A), ("b", printVec dops.showExact P.b),
      ("b_error", printVec dops.showExact P.b_error),
      ("EC", Json.mkObj [("rows", Lean.toJson cPZ.p), ("cols", Lean.toJson P.q),
        ("data", Json.arr ((Array.ofFn fun k : Fin cPZ.p =>
          Array.ofFn fun l : Fin P.q => Lean.toJson (P.R k l)).flatten))]) ])

private def aux_set (dops : DtypeOps 𝕋) (name : String) {n : Nat}
    (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) : String × Json :=
  (name, aux_print dops cPZ.materialise)

/-- Two constrained polynomial zonotopes of one dimension in. -/
private def aux_pair (dops : DtypeOps 𝕋) (req : Json) :
    Except String (Σ n : Nat, ConPolyZono 𝕋 (Vec 𝕋 n) × ConPolyZono 𝕋 (Vec 𝕋 n)) := do
  let d ← aux_parse dops (← field req "cPZ")
  let (b, _) ← aux_parseFixed dops d.n (← field req "cPZ2")
  pure ⟨d.n, d.cPZ, b⟩

private def aux_unary (op : String) (dops : DtypeOps 𝕋) (req : Json)
    (f : {n : Nat} → ConPolyZono 𝕋 (Vec 𝕋 n) → ConPolyZono 𝕋 (Vec 𝕋 n)) : Resp := do
  checkFields op req ["cPZ"]
  let d ← aux_parse dops (← field req "cPZ")
  pure [aux_set dops "cPZ" (f d.cPZ)]

private def aux_binary (op : String) (dops : DtypeOps 𝕋) (req : Json)
    (f : {n : Nat} → ConPolyZono 𝕋 (Vec 𝕋 n) → ConPolyZono 𝕋 (Vec 𝕋 n) →
      ConPolyZono 𝕋 (Vec 𝕋 n)) : Resp := do
  checkFields op req ["cPZ", "cPZ2"]
  let ⟨_, a, b⟩ ← aux_pair dops req
  pure [aux_set dops "cPZ" (f a b)]

/-- The factor the request's identifier `factor` names. -/
private def aux_factor (req : Json) (d : DynConPolyZono 𝕋) : Except String (Fin d.cPZ.p) := do
  let id ← natField req "factor"
  match d.id.findIdx? (· == id) with
  | some r => if h : r < d.cPZ.p then pure ⟨r, h⟩ else throw "internal: identifiers and factors"
  | none => throw s!"{id} is not an identifier of the set"

/-- Two halves as the response. -/
private def aux_halves (dops : DtypeOps 𝕋) {n : Nat}
    (H : ConPolyZono 𝕋 (Vec 𝕋 n) × ConPolyZono 𝕋 (Vec 𝕋 n)) : List (String × Json) :=
  [aux_set dops "cPZ1" H.1, aux_set dops "cPZ2" H.2]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `conPolyZono.cartProd`: the sets side by side, each on its own factors. -/
def handleConPolyZonoCartProd (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "cartProd" req ["cPZ", "cPZ2"]
  let a ← aux_parse dops (← field req "cPZ")
  let b ← aux_parse dops (← field req "cPZ2")
  pure [aux_set dops "cPZ" (ConPolyZono.cartProd a.cPZ b.cPZ)]

/-- `conPolyZono.mtimes`: `M cPZ`, `M` a matrix. -/
def handleConPolyZonoMtimes (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "mtimes" req ["cPZ", "M"]
  let d ← aux_parse dops (← field req "cPZ")
  let ⟨_, M⟩ ← parseMatColsFixed dops.readExact d.n (← field req "M")
  pure [aux_set dops "cPZ" (ConPolyZono.mtimes M d.cPZ)]

/-- `conPolyZono.exactPlus`: the sum over the same factors; both sets need as many. -/
def handleConPolyZonoExactPlus (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "exactPlus" req ["cPZ", "cPZ2"]
  let ⟨_, a, b⟩ ← aux_pair dops req
  if hp : a.p = b.p then pure [aux_set dops "cPZ" (ConPolyZono.exactPlus a b hp)]
  else throw s!"exactPlus: the sets have {a.p} and {b.p} factors, they must share them"

/-- `conPolyZono.split`: the halves of the box `I` along coordinate `dim`, intersected with the set
(`ConPolyZono.splitWith`). -/
def handleConPolyZonoSplit (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "split" req ["cPZ", "dim", "I"]
  let d ← aux_parse dops (← field req "cPZ")
  let j ← indexField req "dim" d.n
  let I ← match fieldOpt req "I" with
    | some ij => parseIntervalVecFixed dops.readExact d.n ij
    | none => pure (ConPolyZono.interval d.cPZ)
  pure (aux_halves dops (ConPolyZono.splitWith d.cPZ I j))

/-- `conPolyZono.getSubset`: the factor `factor` (an identifier) as `cen + rad α`. -/
def handleConPolyZonoGetSubset (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "getSubset" req ["cPZ", "factor", "cen", "rad"]
  let d ← aux_parse dops (← field req "cPZ")
  let k ← aux_factor req d
  let cen ← dops.readExact "cen" (← scalarField req "cen")
  let rad ← dops.readExact "rad" (← scalarField req "rad")
  pure [aux_set dops "cPZ" (ConPolyZono.getSubset d.cPZ k cen rad)]

/-- The conversions out: the polynomial part, its zonotope (both blocks, nothing halved), and
its box. -/
def handleConPolyZonoConvert (dops : DtypeOps 𝕋) (op : String) (req : Json) : Resp := do
  checkFields op req ["cPZ"]
  let d ← aux_parse dops (← field req "cPZ")
  match op with
  | "polyZonotope" =>
    pure [("P", printPolyZonotope dops.showExact (ConPolyZono.polyZonotope d.cPZ))]
  | "zonotope" => pure [("Z", printZonotope dops.showExact (ConPolyZono.zonotope d.cPZ))]
  | _ => pure [("I", printIntervalVec dops.showExact (ConPolyZono.interval d.cPZ))]

/-- The conversions in: a zonotope (`Z`), a polynomial zonotope (`P`) or a constrained zonotope
(`cZ`) as a constrained polynomial zonotope. -/
def handleConPolyZonoOf (dops : DtypeOps 𝕋) (op : String) (req : Json) : Resp := do
  match op with
  | "ofZonotope" =>
    checkFields op req ["Z"]
    let z ← parseZonotope dops.readExact (← field req "Z")
    pure [aux_set dops "cPZ" (Zonotope.conPolyZono z.Z)]
  | "ofPolyZonotope" =>
    checkFields op req ["P"]
    let pj ← field req "P"
    let ⟨n, _⟩ ← parseVecDyn dops.readExact (← field pj "c")
    let pZ ← parsePolyZonotopeFixed dops.readExact n pj
    pure [aux_set dops "cPZ" (PolyZonotope.conPolyZono pZ)]
  | _ =>
    checkFields op req ["cZ"]
    let d ← parseConZonotope dops.readExact (← field req "cZ")
    pure [aux_set dops "cPZ" (ConZonotope.conPolyZono d.cZ)]

/-- Every op of this file, without the `conPolyZono.` prefix. -/
def conPolyZonoOpNames : List String :=
  [ "and", "cartProd", "center", "compact", "convHull", "dim", "empty", "exactPlus", "getSubset",
    "interval", "isequal", "lift", "linComb", "mtimes", "ofConZonotope", "ofPolyZonotope",
    "ofZonotope", "origin", "plus", "polyZonotope", "project", "reduce", "representsa", "split",
    "splitDepFactor", "splitLongestGen", "zonotope" ]

/-- `op` of `conPolyZono.`, run; `none` for a name this file does not serve. -/
@[noinline, nospecialize]
def handleConPolyZonoOp (dops : DtypeOps 𝕋) (op : String) (req : Json) : Option Resp :=
  match op with
  | "and" => some (aux_binary op dops req fun a b => ConPolyZono.intersection a b)
  | "cartProd" => some (handleConPolyZonoCartProd dops req)
  | "center" => some (do
      checkFields op req ["cPZ"]
      let d ← aux_parse dops (← field req "cPZ")
      pure [("c", printVec dops.showExact (ConPolyZono.center d.cPZ))])
  | "compact" => some (do
      checkStrOption op req "method" "all"
      checkTol op req
      checkFields op req ["cPZ", "method", "tol"]
      let d ← aux_parse dops (← field req "cPZ")
      pure [aux_set dops "cPZ" (ConPolyZono.compact d.cPZ)])
  | "convHull" => some (aux_binary op dops req fun a b => ConPolyZono.convHull a b)
  | "dim" => some (do
      checkFields op req ["cPZ"]
      let d ← aux_parse dops (← field req "cPZ")
      pure [("value", Lean.toJson d.n)])
  -- the arms from `empty` on
  | "empty" => some (do
      checkFields op req ["n"]
      pure [aux_set dops "cPZ" (ConPolyZono.empty (𝕋 := 𝕋) (← natField req "n"))])
  | "exactPlus" => some (handleConPolyZonoExactPlus dops req)
  | "getSubset" => some (handleConPolyZonoGetSubset dops req)
  | "isequal" => some (do
      checkFields op req ["cPZ", "cPZ2", "tol"]
      checkTol op req
      let ⟨_, a, b⟩ ← aux_pair dops req
      valueBool (ConPolyZono.isequal a b))
  | "lift" => some (do
      checkFields op req ["cPZ", "N", "dims"]
      let d ← aux_parse dops (← field req "cPZ")
      let e ← liftPerm req d.n
      pure [aux_set dops "cPZ" (ConPolyZono.reindex e.symm d.cPZ)])
  | "linComb" => some (aux_binary op dops req fun a b => ConPolyZono.linComb a b)
  -- the arms from `mtimes` on
  | "mtimes" => some (handleConPolyZonoMtimes dops req)
  | "ofZonotope" | "ofPolyZonotope" | "ofConZonotope" => some (handleConPolyZonoOf dops op req)
  | "origin" => some (do
      checkFields op req ["n"]
      pure [aux_set dops "cPZ" (ConPolyZono.origin (𝕋 := 𝕋) (← natField req "n"))])
  | "plus" => some (aux_binary op dops req fun a b => ConPolyZono.plus a b)
  | "polyZonotope" | "zonotope" | "interval" => some (handleConPolyZonoConvert dops op req)
  | "project" => some (do
      checkFields op req ["cPZ", "dims"]
      let d ← aux_parse dops (← field req "cPZ")
      let ⟨_, dims⟩ ← indexArrField req "dims" d.n
      pure [aux_set dops "cPZ" (ConPolyZono.project d.cPZ dims)])
  | "reduce" => some (do
      checkFields op req ["cPZ", "order", "method"]
      checkStrOption op req "method" "girard"
      let d ← aux_parse dops (← field req "cPZ")
      pure [aux_set dops "cPZ" (ConPolyZono.reduce d.cPZ (← natField req "order"))])
  -- the arms from `representsa` on
  | "representsa" => some (do
      checkFields op req ["cPZ", "type", "tol"]
      checkTol op req
      checkStrOption op req "type" "point"
      let d ← aux_parse dops (← field req "cPZ")
      valueBool (ConPolyZono.representsa_point d.cPZ))
  | "split" => some (handleConPolyZonoSplit dops req)
  | "splitDepFactor" => some (do
      checkFields op req ["cPZ", "factor"]
      let d ← aux_parse dops (← field req "cPZ")
      pure (aux_halves dops (ConPolyZono.splitDepFactor d.cPZ (← aux_factor req d))))
  | "splitLongestGen" => some (do
      checkFields op req ["cPZ"]
      let d ← aux_parse dops (← field req "cPZ")
      pure (aux_halves dops (ConPolyZono.splitLongestGen d.cPZ)))
  | _ => none

end CORALean.Oracle


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
