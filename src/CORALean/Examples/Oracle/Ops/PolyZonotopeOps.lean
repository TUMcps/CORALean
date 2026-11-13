import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
import CORALean.ContSet.Conversion.Float.Operations.PolyZonotope_to_ZonotopeFold
import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_PolyZonotope
import CORALean.ContSet.Conversion.Float.Theorems.PolyZonotopeZonotopeFoldContains
import CORALean.ContSet.PolyZonotope.Float.Instances
import CORALean.ContSet.PolyZonotope.Float.Operations.Construct
import CORALean.ContSet.PolyZonotope.Float.Theorems.ConstructOuter
import CORALean.ContSet.PolyZonotope.Float.Operations.EncloseShared
import CORALean.ContSet.PolyZonotope.Float.Operations.ReduceSplit
import CORALean.ContSet.PolyZonotope.Float.Theorems.EncloseSharedOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.ReduceSplitOuter
import CORALean.Global.Sort
import CORALean.ContSet.PolyZonotope.Float.Operations.Mtimes
import CORALean.ContSet.PolyZonotope.Float.Operations.OfZonotope
import CORALean.ContSet.PolyZonotope.Float.Operations.Plus
import CORALean.Examples.Oracle.Ops.PolyZonotopeCodec
import CORALean.Examples.Oracle.Ops.PolyZonotopeHash
import CORALean.Examples.Oracle.Ops.SetCodec

/-!
# The polynomial-zonotope ops: CORA's `polyZonotope` methods

Adapters over the float definitions `references/coverage/contSet/polyZonotope.md` links. A set is
`{"c","G","GI","Exp","E","id"}` (`PolyZonotopeCodec.lean`, and the identifiers, `1..p` where the
request has none); the exponent matrix `Exp` is `p × h`. Served: `constructor` (CORA's
`polyZonotope(c, G, GI, E, id)`: the zero generators go, equal exponent columns are added, in the
order of CORA's hash), `plus` (a polynomial zonotope `Q`, a zonotope `Z`, a box `I` or a point `v`),
`mtimes` (`M`), `zonotope` and `interval` (CORA's `zonotope(pZ)` and `interval(pZ)`), `dim`, and
`zonotope.polyZonotope` and `interval.polyZonotope` of the conversions. Indices of the sets are
as CORA's, the identifiers are CORA's integers.

## Inputs
* none

## Output
* the names of the ops served, or the response fields of an op
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Oracle

open CORALean CORALean.Float
open Lean (Json)

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A polynomial zonotope of the dimension read off the request, with its identifiers. -/
private structure DynPolyZonotope (𝕋 : Type) [FloatOps 𝕋] where
  n : Nat
  pZ : PolyZonotope (Vec 𝕋 n)
  id : Array Nat


/-- The set `j` and its identifiers (`1..p` where none are given). -/
private def aux_parse (dops : DtypeOps 𝕋) (j : Json) : Except String (DynPolyZonotope 𝕋) := do
  let ⟨n, _⟩ ← parseVecDyn dops.readExact (← field j "c")
  let pZ ← parsePolyZonotopeFixed dops.readExact n j
  let ids ← match fieldOpt j "id" with
    | some _ => natArrField j "id"
    | none => pure ((Array.range pZ.p).map (· + 1))
  if ids.size ≠ pZ.p then throw s!"`id` has {ids.size} entries, the exponent matrix {pZ.p} rows"
  pure ⟨n, pZ, ids⟩

/-- `pZ` as the wire set, with its identifiers. -/
private def aux_print (dops : DtypeOps 𝕋) {n : Nat} (pZ : PolyZonotope (Vec 𝕋 n))
    (ids : Array Nat) : Json :=
  (printPolyZonotope dops.showExact pZ).setObjVal! "id" (Json.arr (ids.map Lean.toJson))

/-- The generators of `Z` that are not zero (CORA's `zonotope(I)` drops the zero radii). -/
private def aux_zonoDropZero {n : Nat} (Z : Zonotope (Vec 𝕋 n)) : Zonotope (Vec 𝕋 n) :=
  let ks : Array (Fin Z.h) := (Array.ofFn id).filter fun l =>
    !((List.finRange n).all fun i => FloatOps.le (Z.G l i) FloatOps.zero &&
      FloatOps.le FloatOps.zero (Z.G l i))
  { Z with h := ks.size, G := fun j => Z.G (ks[j.val]'j.isLt) }

/-- The polynomial zonotope of a zonotope (CORA's `polyZonotope(Z)`): the identity exponents,
then the constructor. -/
private def aux_ofZonotope {n : Nat} (Z : Zonotope (Vec 𝕋 n)) : PolyZonotope (Vec 𝕋 n) :=
  Z.polyZonotope.construct (hashedColumnOrder #[])


/-- CORA's `reduce(pZ, 'girard', order)` (`PolyZonotope.reduceSplit`, `reduceSplit_outer`), with
the indices of the dependent generators kept. -/
private def aux_reduce {n : Nat} (pZ : PolyZonotope (Vec 𝕋 n)) (o : Nat) :
    PolyZonotope (Vec 𝕋 n) × List Nat :=
  if o * n < pZ.h + pZ.q then
    -- the squared length of generator `r` of `[G, GI]` (CORA ranks longest first, keeps `order`)
    let len : Fin (pZ.h + pZ.q) → 𝕋 := fun r =>
      let x : Fin n → 𝕋 := fun i =>
        Fin.addCases (motive := fun _ => 𝕋)
          (fun l => if ∀ k, pZ.E k l % 2 = 0 then FloatOps.half (pZ.G l i) else pZ.G l i)
          (fun j => pZ.GI j i) r
      sumDown fun i : Fin n => FloatOps.mulDown (x (Fin.rev i)) (x (Fin.rev i))
    let perm := sortPerm fun a b : Fin (pZ.h + pZ.q) => FloatOps.le (len b) (len a)
    let K := (o - 1) * n
    let removed : List (Fin (pZ.h + pZ.q)) :=
      ((List.finRange (pZ.h + pZ.q)).filter (fun t => K ≤ t.val)).map perm
    let rD := (removed.filter (fun r => r.val < pZ.h)).map Fin.val
    let rI := (removed.filter (fun r => pZ.h ≤ r.val)).map (fun r => r.val - pZ.h)
    let kD := (List.range pZ.h).filter (fun l => !rD.contains l)
    (pZ.reduceSplit kD.toArray rD.toArray
      ((List.range pZ.q).filter (fun j => !rI.contains j)).toArray rI.toArray
      (hashedColumnOrder #[]), kD)
  else (pZ.compactFactors, List.range pZ.h)

/-- The identifiers some kept dependent generator still reads. -/
private def aux_usedIds {n : Nat} (pZ : PolyZonotope (Vec 𝕋 n)) (kept : List Nat)
    (ids : Array Nat) : Array Nat :=
  (Array.ofFn fun k : Fin pZ.p => k).filterMap fun k =>
    if kept.any (fun l => if hl : l < pZ.h then pZ.E k ⟨l, hl⟩ != 0 else false) then ids[k.val]?
    else none

/-- `P + Z` for a zonotope `Z` (independent generators), as the response. -/
private def aux_plusZ (dops : DtypeOps 𝕋) (d : DynPolyZonotope 𝕋) (z : Zonotope (Vec 𝕋 d.n)) :
    List (String × Json) :=
  [("P", aux_print dops (d.pZ.plus (Zonotope.ofIndep z)).materialise d.id)]

/-- The exponent matrix as rows of columns. -/
private def aux_rows {n : Nat} (P : PolyZonotope (Vec 𝕋 n)) : Array (Array Nat) :=
  Array.ofFn fun k : Fin P.p => Array.ofFn fun l : Fin P.h => P.E k l

/-- CORA's `enclose(pZ, pZ2)` (`PolyZonotope.encloseShared`, `encloseShared_outer`), with the
identifiers of the result. -/
private def aux_enclose {n : Nat} (P Q : PolyZonotope (Vec 𝕋 n)) (idP idQ : Array Nat) :
    Except String (PolyZonotope (Vec 𝕋 n) × Array Nat) := do
  -- equal identifiers and exponents: enclose over the common factors; otherwise pad to the union
  if idP == idQ && aux_rows P == aux_rows Q then
    if hh : Q.h = P.h then
      let ids := idP.push (idP.foldl max 0 + 1)
      pure ((P.encloseShared Q hh).construct (hashedColumnOrder #[]), ids)
    else throw "enclose: internal, the exponent matrices differ in size"
  else
    -- CORA adds the constant columns of both sets to the center; this pipeline does not
    if P.h > 0 && (List.finRange P.h).any (fun l => (List.finRange P.p).all fun k => P.E k l == 0)
        || Q.h > 0 &&
          (List.finRange Q.h).any (fun l => (List.finRange Q.p).all fun k => Q.E k l == 0)
    then throw "enclose: a set with a constant dependent generator and other identifiers is not \
      served (CORA folds the constant generators into the center, this pipeline does not)"
    -- the union of the identifiers, sorted; the rows of each set over it
    let ids := (idP ++ idQ).qsort (· < ·) |>.toList.eraseDups.toArray
    let rowsP := aux_rows P
    let rowsQ := aux_rows Q
    let at' (rows : Array (Array Nat)) (idv : Array Nat) (id : Nat) (l : Nat) : Nat :=
      match idv.findIdx? (· == id) with
      | some r => (rows.getD r #[]).getD l 0
      | none => 0
    let E' : Fin ids.size → Fin (P.h + Q.h) → Nat := fun k l =>
      if l.val < P.h then at' rowsP idP (ids[k.val]!) l.val
      else at' rowsQ idQ (ids[k.val]!) (l.val - P.h)
    let zero' : Vec 𝕋 n := fun _ => FloatOps.zero
    let P' : PolyZonotope (Vec 𝕋 n) :=
      { p := ids.size, h := P.h + Q.h, q := P.q, c := P.c, G := Fin.append P.G (fun _ => zero'),
        E := E', GI := P.GI, I_error := P.I_error }
    let Q' : PolyZonotope (Vec 𝕋 n) :=
      { p := ids.size, h := P.h + Q.h, q := Q.q, c := Q.c, G := Fin.append (fun _ => zero') Q.G,
        E := E', GI := Q.GI, I_error := Q.I_error }
    -- CORA has the new factor alone as the sum of two columns, the centers' difference
    let beta : Array Nat :=
      (Array.range (ids.size + 1)).map fun k => if k == ids.size then 1 else 0
    -- the padded sets as arrays (read often), and CORA's constructor again: a cancelled sum goes
    let merged := ((P'.materialise.encloseShared Q'.materialise rfl).construct
      (hashedColumnOrder #[beta])).materialise
    pure (merged.construct (hashedColumnOrder #[]), ids.push (ids.foldl max 0 + 1))


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every op of `polyZonotope.`, without the prefix. -/
def polyZonotopeOpNames : List String :=
  [ "constructor", "plus", "mtimes", "zonotope", "interval", "reduce", "enclose", "dim" ]

/-- `op` of `polyZonotope.`, run; `none` for a name this file does not serve. -/
@[noinline, nospecialize]
def handlePolyZonotopeOp (dops : DtypeOps 𝕋) (op : String) (req : Json) : Option Resp :=
  match op with
  -- CORA's `polyZonotope(c, G, GI, E, id)`
  | "constructor" => some (do
    checkFields op req ["P"]
    let d ← aux_parse dops (← field req "P")
    pure [("P", aux_print dops (d.pZ.construct (hashedColumnOrder #[])).materialise d.id)])
  | "dim" => some (do
    checkFields op req ["P"]
    let d ← aux_parse dops (← field req "P")
    pure [("value", Lean.toJson d.n)])
  -- `zonotope(pZ)`
  | "zonotope" => some (do
    checkFields op req ["P"]
    let d ← aux_parse dops (← field req "P")
    pure [("Z", printZonotope dops.showExact d.pZ.zonotopeFold)])
  | "interval" => some (do
    checkFields op req ["P"]
    let d ← aux_parse dops (← field req "P")
    pure [("I", printIntervalVec dops.showExact d.pZ.zonotopeFold.interval)])
  -- `reduce(pZ, 'girard', order)`
  | "reduce" => some (do
    checkFields op req ["P", "order", "method"]
    if let some m := fieldOpt req "method" then
      if m.getStr?.toOption != some "girard" then throw "reduce: `method` must be `girard`"
    let d ← aux_parse dops (← field req "P")
    let o ← natField req "order"
    if o = 0 then throw "reduce: the order must be at least 1"
    let (R, kept) := aux_reduce d.pZ o
    let ids := aux_usedIds d.pZ kept d.id
    if R.p ≠ ids.size then throw "reduce: the factors kept do not match the result (internal)"
    pure [("P", aux_print dops R.materialise ids)])
  -- `enclose(pZ, pZ2)`
  | "enclose" => some (do
    checkFields op req ["P", "Q"]
    let d ← aux_parse dops (← field req "P")
    let e ← aux_parse dops (← field req "Q")
    if h : e.n = d.n then
      let Q : PolyZonotope (Vec 𝕋 d.n) := h ▸ e.pZ
      let (R, ids) ← aux_enclose d.pZ Q d.id e.id
      if R.p ≠ ids.size then throw "enclose: the identifiers do not match the factors (internal)"
      pure [("P", aux_print dops R.materialise ids)]
    else throw s!"enclose: the sets differ in dimension, {d.n} and {e.n}")
  | "mtimes" => some (do
    checkFields op req ["M", "P"]
    let d ← aux_parse dops (← field req "P")
    let ⟨_, M⟩ ← parseMatColsFixed dops.readExact d.n (← field req "M")
    pure [("P", aux_print dops (PolyZonotope.mtimes M d.pZ).materialise d.id)])
  -- `pZ + (Q | Z | I | v)`
  | "plus" => some (do
    checkFields op req ["P", "Q", "Z", "I", "v"]
    let d ← aux_parse dops (← field req "P")
    match fieldOpt req "Q", fieldOpt req "Z", fieldOpt req "I", fieldOpt req "v" with
    | some qj, none, none, none =>
      -- the factors of Q get the identifiers above those of P
      let e ← aux_parse dops qj
      if h : e.n = d.n then
        let Q : PolyZonotope (Vec 𝕋 d.n) := h ▸ e.pZ
        let shift := d.id.foldl max 0
        pure [("P", aux_print dops (d.pZ.plus Q).materialise (d.id ++ e.id.map (shift + ·)))]
      else throw s!"plus: the sets differ in dimension, {d.n} and {e.n}"
    | none, some zj, none, none =>
      let z ← parseZonotopeFixed dops.readExact d.n zj
      pure (aux_plusZ dops d z)
    | none, none, some ij, none =>
      let b ← parseIntervalVecFixed dops.readExact d.n ij
      let z := aux_zonoDropZero (Interval.zonotope b)
      pure (aux_plusZ dops d z)
    | none, none, none, some vj =>
      let v ← parseVecFixed dops.readExact d.n vj
      let z : Zonotope (Vec 𝕋 d.n) :=
        ⟨0, v, Fin.elim0, ⟨fun _ => FloatOps.zero, fun _ => FloatOps.zero⟩⟩
      pure (aux_plusZ dops d z)
    | _, _, _, _ => throw "plus: needs exactly one of `Q`, `Z`, `I` and `v`")
  | _ => none

/-- `zonotope.polyZonotope`: `Z` as a polynomial zonotope of the identity exponents. -/
def handleZonotopePolyZonotope (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "polyZonotope" req ["Z"]
  let d ← parseZonotope dops.readExact (← field req "Z")
  let P := aux_ofZonotope d.Z
  pure [("P", aux_print dops P.materialise ((Array.range d.Z.h).map (· + 1)))]

/-- `interval.polyZonotope`: `I` as a polynomial zonotope (CORA's `polyZonotope(I)`). -/
def handleIntervalPolyZonotope (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "polyZonotope" req ["I"]
  let b ← parseBox dops.readExact (← field req "I")
  let P := aux_ofZonotope (Interval.zonotope b.I)
  pure [("P", aux_print dops P.materialise ((Array.range b.n).map (· + 1)))]

end CORALean.Oracle


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
