import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
import CORALean.ContSet.Conversion.Float.Operations.PolyZonotope_to_ZonotopeFold
import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_PolyZonotope
import CORALean.ContSet.Conversion.Float.Theorems.PolyZonotopeZonotopeFoldContains
import CORALean.ContSet.PolyZonotope.Float.Instances
import CORALean.ContSet.PolyZonotope.Float.Operations.CartProd
import CORALean.ContSet.PolyZonotope.Float.Operations.Construct
import CORALean.ContSet.PolyZonotope.Float.Operations.ExactPlus
import CORALean.ContSet.PolyZonotope.Float.Operations.QuadMapCora
import CORALean.ContSet.PolyZonotope.Float.Theorems.QuadMapCoraOuter
import CORALean.ContSet.PolyZonotope.Float.Operations.SplitLongest
import CORALean.ContSet.PolyZonotope.Float.Theorems.SplitLongestOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.CartProdExact
import CORALean.ContSet.PolyZonotope.Float.Theorems.ExactPlusOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.ConstructOuter
import CORALean.ContSet.PolyZonotope.Float.Operations.EncloseShared
import CORALean.ContSet.PolyZonotope.Float.Operations.EvalPowers
import CORALean.ContSet.PolyZonotope.Float.Theorems.EvalPowersOuter
import CORALean.ContSet.PolyZonotope.Float.Operations.ReduceCora
import CORALean.ContSet.PolyZonotope.Float.Theorems.EncloseSharedOuter
import CORALean.ContSet.PolyZonotope.Float.Operations.Mtimes
import CORALean.ContSet.PolyZonotope.Float.Operations.OfZonotope
import CORALean.ContSet.PolyZonotope.Float.Operations.Plus
import CORALean.Examples.Oracle.Ops.PolyZonotopeCodec
import CORALean.Examples.Oracle.Ops.PolyZonotopeHash
import CORALean.Examples.Oracle.Ops.SetCodec
import CORALean.ContSet.Zonotope.Float.Instances

/-!
# The polynomial-zonotope ops: CORA's `polyZonotope` methods

Adapters over the float definitions `references/coverage/contSet/polyZonotope.md` links. A set is
`{"c","G","GI","Exp","E","id"}` (`PolyZonotopeCodec.lean`; identifiers `1..p` where none; `Exp` is
`p × h`). Served: `constructor` (CORA's `polyZonotope(c, G, GI, E, id)`: zero generators go, equal
exponent columns are added in the order of CORA's hash), `plus` (`Q`, `Z`, a box `I` or a point
`v`), `mtimes` (`M`), `zonotope`, `interval`, `dim`, `evalPowers` (`coeffs` a row per coordinate,
lowest degree first), `center`, `cartProd` (`Z`), `exactPlus`, `isIntersecting` (`S`, `'approx'`),
`splitDepFactor` (`factor`, an identifier), `splitLongestGen`, `quadMap` (`Q`, matrices),
`zonotope.polyZonotope`, `interval.polyZonotope`; indices and identifiers are CORA's.

## Inputs
* none

## Output
* the names of the ops served, or the response fields of an op
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       13-November-2026
-- Last update:   20-November-2026
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
  pure ⟨n, pZ, ← parsePolyZonotopeIds pZ j⟩

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


/-- `P + Z` for a zonotope `Z` (independent generators), as the response. -/
private def aux_plusZ (dops : DtypeOps 𝕋) (d : DynPolyZonotope 𝕋) (z : Zonotope (Vec 𝕋 d.n)) :
    List (String × Json) :=
  [("P", printPolyZonotopeIds dops.showExact (d.pZ.plus (Zonotope.ofIndep z)).materialise d.id)]

/-- The exponent matrix as rows of columns. -/
private def aux_rows {n : Nat} (P : PolyZonotope (Vec 𝕋 n)) : Array (Array Nat) :=
  Array.ofFn fun k : Fin P.p => Array.ofFn fun l : Fin P.h => P.E k l

/-- The independent generators that are not zero, in their order (CORA.cpp's constructor drops the
zero ones; they add nothing to the set). -/
private def aux_dropZeroIndep {n : Nat} (P : PolyZonotope (Vec 𝕋 n)) : PolyZonotope (Vec 𝕋 n) :=
  let ks : Array (Fin P.q) := (Array.ofFn id).filter fun j =>
    !((List.finRange n).all fun i => FloatOps.le (P.GI j i) FloatOps.zero &&
      FloatOps.le FloatOps.zero (P.GI j i))
  { P with q := ks.size, GI := fun j => P.GI (ks[j.val]'j.isLt) }

/-- The dependent and independent generators that are not zero, in their order, the exponents
kept (CORA.cpp's constructor on columns it does not merge). -/
private def aux_dropZero {n : Nat} (P : PolyZonotope (Vec 𝕋 n)) : PolyZonotope (Vec 𝕋 n) :=
  let live : Array ℕ := ((List.finRange P.h).filter fun l =>
    !(List.finRange n).all fun i => FloatOps.le (P.G l i) FloatOps.zero &&
      FloatOps.le FloatOps.zero (P.G l i)).toArray.map Fin.val
  aux_dropZeroIndep (P.pick live.size fun t => live[t.val]!)

/-- The two halves of a split through CORA's constructor, the zero independent generators
dropped. -/
private def aux_halves (dops : DtypeOps 𝕋) {n : Nat}
    (H : PolyZonotope (Vec 𝕋 n) × PolyZonotope (Vec 𝕋 n)) (ids : Array Nat) :
    List (String × Json) :=
  let out := fun P : PolyZonotope (Vec 𝕋 n) => printPolyZonotopeIds dops.showExact
    (aux_dropZeroIndep (P.construct (hashedColumnOrder #[]))).materialise ids
  [("P1", out H.1), ("P2", out H.2)]

/-- Two sets over the union of their identifiers, sorted (CORA's `mergeExpMatrix`): the
exponent rows of each set placed at its identifiers, zero at the others. -/
private structure Aligned (𝕋 : Type) [FloatOps 𝕋] (n : Nat) where
  ids : Array Nat
  P : PolyZonotope (Vec 𝕋 n)
  Q : PolyZonotope (Vec 𝕋 n)
  hp : P.p = Q.p

/-- `P` and `Q` over the sorted union of the identifiers `idP` and `idQ`. -/
private def aux_align {n : Nat} (P Q : PolyZonotope (Vec 𝕋 n)) (idP idQ : Array Nat) :
    Aligned 𝕋 n :=
  let ids := (idP ++ idQ).qsort (· < ·) |>.toList.eraseDups.toArray
  let rowsP := aux_rows P
  let rowsQ := aux_rows Q
  let at' (rows : Array (Array Nat)) (idv : Array Nat) (id : Nat) (l : Nat) : Nat :=
    match idv.findIdx? (· == id) with
    | some r => (rows.getD r #[]).getD l 0
    | none => 0
  ⟨ids, { P with p := ids.size, E := fun k l => at' rowsP idP (ids[k.val]!) l.val },
    { Q with p := ids.size, E := fun k l => at' rowsQ idQ (ids[k.val]!) l.val }, rfl⟩

/-- The box of the image of `Z` under the rows `A` (CORA.cpp's `Z.linear_map(A).interval()`). -/
private def aux_rowBox {m n : Nat} (A : Fin m → Vec 𝕋 n) (Z : Zonotope (Vec 𝕋 n)) :
    Interval (Vec 𝕋 m) :=
  let M : Mat 𝕋 m n := fun i j => A i j
  (Mtimes.mtimes (ContSet := 𝒵[𝕋]) M Z).interval

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
  [ "constructor", "plus", "mtimes", "zonotope", "interval", "reduce", "enclose", "dim",
    "evalPowers", "center", "cartProd", "exactPlus",
    "isIntersecting", "splitDepFactor", "splitLongestGen", "quadMap" ]

/-- `op` of `polyZonotope.`, run; `none` for a name this file does not serve. -/
@[noinline, nospecialize]
def handlePolyZonotopeOp (dops : DtypeOps 𝕋) (op : String) (req : Json) : Option Resp :=
  match op with
  -- CORA's `polyZonotope(c, G, GI, E, id)`
  | "constructor" => some (do
    checkFields op req ["P"]
    let d ← aux_parse dops (← field req "P")
    let R := (d.pZ.construct (hashedColumnOrder #[])).materialise
    pure [("P", printPolyZonotopeIds dops.showExact R d.id)])
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
    let (R, kept) := d.pZ.reduceCora o (hashedColumnOrder #[])
    let ids := usedPolyZonotopeIds d.pZ kept d.id
    if R.p ≠ ids.size then throw "reduce: the factors kept do not match the result (internal)"
    pure [("P", printPolyZonotopeIds dops.showExact R.materialise ids)])
  -- `enclose(pZ, pZ2)`
  | "enclose" => some (do
    checkFields op req ["P", "Q"]
    let d ← aux_parse dops (← field req "P")
    let e ← aux_parse dops (← field req "Q")
    if h : e.n = d.n then
      let Q : PolyZonotope (Vec 𝕋 d.n) := h ▸ e.pZ
      let (R, ids) ← aux_enclose d.pZ Q d.id e.id
      if R.p ≠ ids.size then throw "enclose: the identifiers do not match the factors (internal)"
      pure [("P", printPolyZonotopeIds dops.showExact R.materialise ids)]
    else throw s!"enclose: the sets differ in dimension, {d.n} and {e.n}")
  -- the polynomials `coeffs` (a row per coordinate) by the powers of each row
  | "evalPowers" => some (do
    checkFields op req ["P", "coeffs"]
    let d ← aux_parse dops (← field req "P")
    let ⟨K, C⟩ ← parseMatRowsFixed dops.readExact d.n (← field req "coeffs")
    if K = 0 then throw "evalPowers: `coeffs` needs at least one column"
    let R := (d.pZ.evalPowers (List.ofFn fun k i => C i k)).materialise
    pure [("P", printPolyZonotopeIds dops.showExact R d.id)])
  | "mtimes" => some (do
    checkFields op req ["M", "P"]
    let d ← aux_parse dops (← field req "P")
    let ⟨_, M⟩ ← parseMatColsFixed dops.readExact d.n (← field req "M")
    let R := (PolyZonotope.mtimes M d.pZ).materialise
    pure [("P", printPolyZonotopeIds dops.showExact R d.id)])
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
        pure [("P", printPolyZonotopeIds dops.showExact (d.pZ.plus Q).materialise
          (d.id ++ e.id.map (shift + ·)))]
      else throw s!"plus: the sets differ in dimension, {d.n} and {e.n}"
    | none, some zj, none, none =>
      let z ← parseZonotopeFixed dops.readExact d.n zj
      pure (aux_plusZ dops d z)
    | none, none, some ij, none =>
      let b ← parseIntervalVecFixed dops.readExact d.n ij
      let z := aux_zonoDropZero (Interval.zonotope b)
      pure (aux_plusZ dops d z)
    | none, none, none, some vj =>
      -- a point is a zonotope without generators
      let v ← parseVecFixed dops.readExact d.n vj
      let z : Zonotope (Vec 𝕋 d.n) :=
        ⟨0, v, Fin.elim0, ⟨fun _ => FloatOps.zero, fun _ => FloatOps.zero⟩⟩
      pure (aux_plusZ dops d z)
    | _, _, _, _ => throw "plus: needs exactly one of `Q`, `Z`, `I` and `v`")
  -- `center(pZ)`, the field `c`
  | "center" => some (do
    checkFields op req ["P"]
    let d ← aux_parse dops (← field req "P")
    pure [("c", printVec dops.showExact d.pZ.center)])
  -- `cartProd(pZ, Z)`: the zonotope's generators independent, the factors the set's
  | "cartProd" => some (do
    checkFields op req ["P", "Z"]
    let d ← aux_parse dops (← field req "P")
    let z ← parseZonotope dops.readExact (← field req "Z")
    let R := aux_dropZero (d.pZ.cartProd (Zonotope.ofIndep z.Z))
    pure [("P", printPolyZonotopeIds dops.showExact R.materialise d.id)])
  -- `exactPlus(pZ, pZ2)`: both over the union of the identifiers, then CORA's constructor
  | "exactPlus" => some (do
    checkFields op req ["P", "Q"]
    let d ← aux_parse dops (← field req "P")
    let e ← aux_parse dops (← field req "Q")
    if h : e.n = d.n then
      let Q : PolyZonotope (Vec 𝕋 d.n) := h ▸ e.pZ
      let A := aux_align d.pZ Q d.id e.id
      let R := aux_dropZeroIndep ((A.P.exactPlus A.Q A.hp).construct (hashedColumnOrder #[]))
      pure [("P", printPolyZonotopeIds dops.showExact R.materialise A.ids)]
    else throw s!"exactPlus: the sets differ in dimension, {d.n} and {e.n}")
  -- `isIntersecting_(pZ, S, 'approx')`: `false` (certain) if the box of `A zonotope(pZ)` misses
  | "isIntersecting" => some (do
    checkFields op req ["P", "S", "tol"]
    let d ← aux_parse dops (← field req "P")
    let H ← parseHPolytopeFixed dops.readExact d.n (← field req "S")
    let tol ← match fieldOpt req "tol" with
      | none => pure FloatOps.zero
      | some _ => dops.readExact "tol" (← scalarField req "tol")
    let Z := d.pZ.zonotopeFold
    -- the boxes of the images of the zonotope under the rows
    let B := aux_rowBox H.A Z
    let Be := aux_rowBox H.Ae Z
    let below := (List.finRange H.m).any fun i => FloatOps.ltStrict (H.b i) (B.inf i)
    let outside := (List.finRange H.me).any fun i =>
      FloatOps.ltStrict (H.be i) (subDown (Be.inf i) tol) ||
        FloatOps.ltStrict (FloatOps.addUp (Be.sup i) tol) (H.be i)
    pure [("value", Lean.toJson !(below || outside))])
  -- `splitDepFactor(pZ, factor)` and `splitLongestGen(pZ)`: the halves `[0, 1]` and `[-1, 0]`
  | "splitDepFactor" => some (do
    checkFields op req ["P", "factor"]
    let d ← aux_parse dops (← field req "P")
    let id ← natField req "factor"
    match d.id.findIdx? (· == id) with
    | some r =>
      if h : r < d.pZ.p then
        pure (aux_halves dops (d.pZ.splitFactor ⟨r, h⟩) d.id)
      else throw "splitDepFactor: internal, the identifiers do not match the factors"
    | none => throw s!"splitDepFactor: {id} is not an identifier of the set")
  | "splitLongestGen" => some (do
    checkFields op req ["P"]
    let d ← aux_parse dops (← field req "P")
    match d.pZ.splitLongest with
    | some H => pure (aux_halves dops H d.id)
    | none => throw "splitLongestGen: the set has no dependent generator")
  -- `quadMap(pZ, Q)` as CORA.cpp computes it, the zero independent generators dropped
  | "quadMap" => some (do
    checkFields op req ["P", "Q"]
    let d ← aux_parse dops (← field req "P")
    let qs ← (← arrField req "Q").mapM fun j => do
      let ⟨r, M⟩ ← parseMatColsFixed dops.readExact d.n j
      if h : r = d.n then pure (h ▸ M) else throw s!"quadMap: expected {d.n}×{d.n} matrices"
    let R := aux_dropZeroIndep
      (d.pZ.quadMapCora (m := qs.size) (fun k => qs[k]) (hashedColumnOrder #[]))
    pure [("P", printPolyZonotopeIds dops.showExact R.materialise d.id)])
  | _ => none

/-- `zonotope.polyZonotope`: `Z` as a polynomial zonotope of the identity exponents. -/
def handleZonotopePolyZonotope (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "polyZonotope" req ["Z"]
  let d ← parseZonotope dops.readExact (← field req "Z")
  let P := aux_ofZonotope d.Z
  pure [("P", printPolyZonotopeIds dops.showExact P.materialise
    ((Array.range d.Z.h).map (· + 1)))]

/-- `interval.polyZonotope`: `I` as a polynomial zonotope (CORA's `polyZonotope(I)`). -/
def handleIntervalPolyZonotope (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "polyZonotope" req ["I"]
  let b ← parseBox dops.readExact (← field req "I")
  let P := aux_ofZonotope (Interval.zonotope b.I)
  pure [("P", printPolyZonotopeIds dops.showExact P.materialise
    ((Array.range b.n).map (· + 1)))]

end CORALean.Oracle


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
