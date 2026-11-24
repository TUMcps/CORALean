import CORALean.ContSet.PolyZonotope.Float.Instances
import CORALean.ContSet.PolyZonotope.Float.Operations.ConvHull
import CORALean.ContSet.PolyZonotope.Float.Operations.CompactFactors
import CORALean.ContSet.PolyZonotope.Float.Operations.Construct
import CORALean.ContSet.PolyZonotope.Float.Operations.FoldConstants
import CORALean.ContSet.PolyZonotope.Float.Operations.CubMap
import CORALean.ContSet.PolyZonotope.Float.Operations.GetSubset
import CORALean.ContSet.PolyZonotope.Float.Operations.Jacobian
import CORALean.ContSet.PolyZonotope.Float.Operations.LinComb
import CORALean.ContSet.PolyZonotope.Float.Operations.MatMap
import CORALean.ContSet.PolyZonotope.Float.Operations.OuterApprox
import CORALean.ContSet.PolyZonotope.Float.Operations.PartZonotope
import CORALean.ContSet.PolyZonotope.Float.Operations.Isequal
import CORALean.ContSet.PolyZonotope.Float.Operations.IsFullDim
import CORALean.ContSet.PolyZonotope.Float.Operations.NoIndep
import CORALean.ContSet.PolyZonotope.Float.Operations.OnlyId
import CORALean.ContSet.PolyZonotope.Float.Operations.PadBack
import CORALean.ContSet.PolyZonotope.Float.Operations.Reindex
import CORALean.ContSet.PolyZonotope.Float.Operations.ReplaceId
import CORALean.ContSet.PolyZonotope.Float.Operations.RepresentsaPoint
import CORALean.ContSet.PolyZonotope.Float.Operations.Restructure
import CORALean.ContSet.PolyZonotope.Float.Operations.RmId
import CORALean.ContSet.PolyZonotope.Float.Operations.Sum
import CORALean.Examples.Oracle.Ops.PolyZonotopeCodec
import CORALean.Examples.Oracle.Ops.PolyZonotopeHash
import CORALean.Examples.Oracle.Ops.SetCodec

/-!
# The polynomial-zonotope ops, second batch: identifiers, structure and predicates

Adapters over the float definitions that `references/coverage/contSet/polyZonotope.md` links, for
CORA.cpp's methods of the same names. A set is as in `PolyZonotopeOps.lean` (`{"c","G","GI","Exp",
"E","id"}`); the identifiers are CORA's, CORALean's factors are their positions.

Served: `replaceId` (`P`, `idOld`, `idNew`; without `idOld` every identifier is renamed),
`restoreId` (`P`, `ids`), `rmId` (`P`, `ids`, then CORA's constructor), `onlyId` (`P`, `ids`; the
parts `P1`, `P2`), `noIndep`, `lift` (`N`, `dims`), `isBounded`, `isFullDim`, `isequal` (`Q`),
`representsa` (`type` `point`), `sum` (`L`, sets over the factors of `P`), `restructure`.

## Inputs
* none

## Output
* the names of the ops served, or the response fields of an op
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       23-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Oracle

open CORALean CORALean.Float
open Lean (Json)

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A polynomial zonotope of the dimension read off the request, with its identifiers. -/
private structure Dyn (𝕋 : Type) [FloatOps 𝕋] where
  n : Nat
  pZ : PolyZonotope (Vec 𝕋 n)
  id : Array Nat

/-- The set `j` and its identifiers (`1..p` where none are given). -/
private def aux_parse (dops : DtypeOps 𝕋) (j : Json) : Except String (Dyn 𝕋) := do
  let ⟨n, _⟩ ← parseVecDyn dops.readExact (← field j "c")
  let pZ ← parsePolyZonotopeFixed dops.readExact n j
  pure ⟨n, pZ, ← parsePolyZonotopeIds pZ j⟩

/-- The independent generators that are not zero, in their order (CORA.cpp's constructor drops
the zero ones). -/
private def aux_dropZeroIndep {n : Nat} (P : PolyZonotope (Vec 𝕋 n)) : PolyZonotope (Vec 𝕋 n) :=
  let ks : Array (Fin P.q) := (Array.ofFn id).filter fun j =>
    !((List.finRange n).all fun i => FloatOps.le (P.GI j i) FloatOps.zero &&
      FloatOps.le FloatOps.zero (P.GI j i))
  { P with q := ks.size, GI := fun j => P.GI (ks[j.val]'j.isLt) }

/-- CORA.cpp's constructor on a set: zero generators dropped, equal exponent columns added in the
order of CORA's hash. -/
private def aux_construct {n : Nat} (P : PolyZonotope (Vec 𝕋 n)) : PolyZonotope (Vec 𝕋 n) :=
  aux_dropZeroIndep (P.construct (hashedColumnOrder #[]))

/-- CORA's ending of `getSubset`: equal columns merged, the constants into the center, the factors
no column reads dropped (with their identifiers). -/
private def aux_merged {n : Nat} (R : PolyZonotope (Vec 𝕋 n)) (id : Array Nat) :
    PolyZonotope (Vec 𝕋 n) × Array Nat :=
  let F : PolyZonotope (Vec 𝕋 n) := (R.construct (hashedColumnOrder #[])).foldConstants
  let used := (Array.range F.p).filter fun k =>
    (List.range F.h).any fun l => if hk : k < F.p then
      if hl : l < F.h then F.E ⟨k, hk⟩ ⟨l, hl⟩ != 0 else false else false
  (aux_dropZeroIndep F.compactFactors, used.map fun k => id.getD k 0)

/-- The factors whose identifier is one of `ids`. -/
private def aux_factors {n : Nat} (P : PolyZonotope (Vec 𝕋 n)) (id ids : Array Nat) :
    Finset (Fin P.p) :=
  Finset.univ.filter fun k => ids.contains (id.getD k.val 0)

/-- The identifiers of `ids` that are not among `known`, in order, each once. -/
private def aux_fresh (known ids : Array Nat) : Array Nat :=
  ids.foldl (fun acc i => if known.contains i || acc.contains i then acc else acc.push i) #[]

/-- The position of `id` in `ids`, as a position of `Fin m` (`m` is `ids.size`, and positive). -/
private def aux_slot (ids : Array Nat) (id : Nat) (hm : 0 < ids.size) : Fin ids.size :=
  ⟨min ((ids.findIdx? (· == id)).getD 0) (ids.size - 1), by omega⟩

/-- Every identifier of `ids` is one of the set's. -/
private def aux_known (id ids : Array Nat) (op : String) : Except String Unit :=
  match ids.find? fun i => !id.contains i with
  | some i => throw s!"{op}: {i} is not an identifier of the set"
  | none => pure ()

/-- The sets of `ids` after one `getSubset` each at the value (zero radius), in the order given. -/
private def aux_subsets {n : Nat} (P : PolyZonotope (Vec 𝕋 n)) (pid : Array Nat)
    (pairs : List (Nat × 𝕋)) : PolyZonotope (Vec 𝕋 n) :=
  pairs.foldl (fun R iv =>
    match pid.findIdx? (· == iv.1) with
    | some t => if h : t < R.p then R.getSubset ⟨t, h⟩ iv.2 FloatOps.zero else R
    | none => R) P

/-- A matrix-valued set from a set of the vectors of its columns, one after the other. -/
private def aux_toMat {n k : Nat} (P : PolyZonotope (Vec 𝕋 (k * n))) : PolyZonotope (Mat 𝕋 n k) :=
  let f : Vec 𝕋 (k * n) → Mat 𝕋 n k := fun v i j => v (finProdFinEquiv (j, i))
  ⟨P.p, P.h, P.q, f P.c, fun l => f (P.G l), P.E, fun j => f (P.GI j),
    ⟨f P.I_error.inf, f P.I_error.sup⟩⟩

/-- The reverse of `aux_toMat`: a matrix-valued set as the vectors of its columns. -/
private def aux_ofMat {n m : Nat} (P : PolyZonotope (Mat 𝕋 n m)) : PolyZonotope (Vec 𝕋 (m * n)) :=
  let f : Mat 𝕋 n m → Vec 𝕋 (m * n) := fun M idx =>
    M (finProdFinEquiv.symm idx).2 (finProdFinEquiv.symm idx).1
  ⟨P.p, P.h, P.q, f P.c, fun l => f (P.G l), P.E, fun j => f (P.GI j),
    ⟨f P.I_error.inf, f P.I_error.sup⟩⟩

/-- The set over the identifiers `ids` (those of the set among them, zero exponents elsewhere). -/
private def aux_over {α : Type} (P : PolyZonotope α) (idP ids : Array Nat) :
    { Q : PolyZonotope α // Q.p = ids.size } :=
  let rows : Array (Array Nat) :=
    Array.ofFn fun k : Fin P.p => Array.ofFn fun l : Fin P.h => P.E k l
  let at' (id : Nat) (l : Nat) : Nat :=
    match idP.findIdx? (· == id) with
    | some r => (rows.getD r #[]).getD l 0
    | none => 0
  ⟨{ P with p := ids.size, E := fun k l => at' (ids.getD k.val 0) l.val }, rfl⟩

/-- The sorted union of two identifier lists. -/
private def aux_union (a b : Array Nat) : Array Nat :=
  (a ++ b).qsort (· < ·) |>.toList.eraseDups.toArray

/-- Identifiers above the largest of `ids`, one per added factor. -/
private def aux_above (ids : Array Nat) (count : Nat) : Array Nat :=
  (Array.range count).map fun j => ids.foldl max 0 + 1 + j

/-- The product of the matrix-valued sets `A` (`n × k`) and `B` (`k × m`) read from `ja` and `jb`,
both over the sorted union of their identifiers, as the columns of the result's matrices. -/
private def aux_matMap (n k m : Nat) (A : PolyZonotope (Vec 𝕋 (k * n)))
    (B : PolyZonotope (Vec 𝕋 (m * k))) (ja jb : Json) :
    Except String (PolyZonotope (Vec 𝕋 (m * n)) × Array Nat) := do
  let idA ← parsePolyZonotopeIds A ja
  let idB ← parsePolyZonotopeIds B jb
  let ids := aux_union idA idB
  let A' := aux_over (aux_toMat (n := n) (k := k) A) idA ids
  let B' := aux_over (aux_toMat (n := k) (k := m) B) idB ids
  pure (aux_ofMat (PolyZonotope.matMap A'.1 B'.1 (A'.2.trans B'.2.symm)), ids)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every op of `polyZonotope.` served here, without the prefix. -/
def polyZonotopeOpNames2 : List String :=
  [ "replaceId", "restoreId", "rmId", "onlyId", "noIndep", "lift", "isBounded", "isFullDim",
    "isequal", "representsa", "sum", "restructure", "jacobian", "linComb", "convHull", "getSubset",
    "resolve", "matMap", "cubMap", "partZonotope", "outerApprox" ]

/-- `op` of `polyZonotope.`, run; `none` for a name this file does not serve. -/
@[noinline, nospecialize]
def handlePolyZonotopeOp2 (dops : DtypeOps 𝕋) (op : String) (req : Json) : Option Resp :=
  match op with
  -- CORA's `replaceId(pZ, idOld, idNew)`: factors with a common new identifier merge
  | "replaceId" => some (do
    checkFields op req ["P", "idOld", "idNew"]
    let d ← aux_parse dops (← field req "P")
    let idNew ← natArrField req "idNew"
    let idOld ← match fieldOpt req "idOld" with
      | some _ => natArrField req "idOld"
      | none => pure d.id
    if idOld.size ≠ idNew.size then throw "replaceId: idOld and idNew differ in length"
    aux_known d.id idOld op
    -- the identifier of each factor after the renaming, then the distinct ones in order
    let renamed : Array Nat := d.id.map fun i =>
      match idOld.findIdx? (· == i) with
      | some t => idNew.getD t i
      | none => i
    let ids' := renamed.foldl (fun acc i => if acc.contains i then acc else acc.push i) #[]
    if hm : 0 < ids'.size then
      let f : Fin d.pZ.p → Fin ids'.size := fun k => aux_slot ids' (renamed.getD k.val 0) hm
      pure [("P", printPolyZonotopeIds dops.showExact (d.pZ.replaceId f).materialise ids')]
    else
      -- no factors at all: nothing to rename
      pure [("P", printPolyZonotopeIds dops.showExact d.pZ.materialise ids')])
  -- CORA's `restoreId`: the identifiers the set lacks added, unused
  | "restoreId" => some (do
    checkFields op req ["P", "ids"]
    let d ← aux_parse dops (← field req "P")
    let ids ← natArrField req "ids"
    if ids.toList.eraseDups.length ≠ ids.size then throw "restoreId: id must not repeat"
    let fresh := aux_fresh d.id ids
    pure [("P", printPolyZonotopeIds dops.showExact (d.pZ.padBack fresh.size).materialise
      (d.id ++ fresh))])
  -- CORA's `rmId`: the factors fixed to 1, then the constructor merges equal columns
  | "rmId" => some (do
    checkFields op req ["P", "ids"]
    let d ← aux_parse dops (← field req "P")
    let ids ← natArrField req "ids"
    aux_known d.id ids op
    let S := aux_factors d.pZ d.id ids
    let R := (d.pZ.rmId S).construct (hashedColumnOrder #[])
    let kept := d.id.filter fun i => !ids.contains i
    if R.p ≠ kept.size then throw "rmId: the identifiers kept do not match the factors (internal)"
    pure [("P", printPolyZonotopeIds dops.showExact R.materialise kept)])
  -- CORA's `onlyId`: the part that depends on the factors alone, and the rest
  | "onlyId" => some (do
    checkFields op req ["P", "ids"]
    let d ← aux_parse dops (← field req "P")
    let ids ← natArrField req "ids"
    if ids.toList.eraseDups.length ≠ ids.size then throw "onlyId: id must not repeat"
    aux_known d.id ids op
    let S := aux_factors d.pZ d.id ids
    let (A, B) := d.pZ.onlyId S
    let inside := d.id.filter ids.contains
    if A.p ≠ inside.size then throw "onlyId: the identifiers do not match the factors (internal)"
    pure [("P1", printPolyZonotopeIds dops.showExact (aux_construct A).materialise inside),
          ("P2", printPolyZonotopeIds dops.showExact (aux_construct B).materialise d.id)])
  -- CORA's `noIndep`
  | "noIndep" => some (do
    checkFields op req ["P"]
    let d ← aux_parse dops (← field req "P")
    pure [("P", printPolyZonotopeIds dops.showExact d.pZ.noIndep.materialise d.id)])
  -- CORA's `lift_`: the coordinates permuted
  | "lift" => some (do
    checkFields op req ["P", "N", "dims"]
    let d ← aux_parse dops (← field req "P")
    let e ← liftPerm req d.n
    pure [("P", printPolyZonotopeIds dops.showExact (d.pZ.reindex e.symm).materialise d.id)])
  -- a polynomial zonotope is bounded
  | "isBounded" => some (do
    checkFields op req ["P"]
    let _ ← aux_parse dops (← field req "P")
    valueBool true)
  | "isFullDim" => some (do
    checkFields op req ["P", "tol"]
    checkTol op req
    let d ← aux_parse dops (← field req "P")
    valueBool d.pZ.isFullDim)
  -- structural, at tolerance 0: `true` only if the stored data are equal
  | "isequal" => some (do
    checkFields op req ["P", "Q", "tol"]
    checkTol op req
    let d ← aux_parse dops (← field req "P")
    let e ← aux_parse dops (← field req "Q")
    if h : e.n = d.n then
      let Q : PolyZonotope (Vec 𝕋 d.n) := h ▸ e.pZ
      valueBool (d.pZ.isequal Q)
    else valueBool false)
  | "representsa" => some (do
    checkFields op req ["P", "type", "tol"]
    checkTol op req
    let d ← aux_parse dops (← field req "P")
    match fieldOpt req "type" with
    | some t =>
      if t.getStr?.toOption == some "point" then valueBool d.pZ.representsa_point
      else throw "representsa: `type` must be `point`"
    | none => throw "representsa: needs `type`")
  -- CORA's `sum(pZ, L)`: the sets share the identifiers of `P`
  | "sum" => some (do
    checkFields op req ["P", "L"]
    let d ← aux_parse dops (← field req "P")
    let ls ← (← arrField req "L").mapM fun j => do
      let e ← aux_parse dops j
      if h : e.n = d.n then
        let Q : PolyZonotope (Vec 𝕋 d.n) := h ▸ e.pZ
        if hp : Q.p = d.pZ.p then
          if e.id == d.id then pure (⟨Q, hp⟩ : { Q : PolyZonotope (Vec 𝕋 d.n) // Q.p = d.pZ.p })
          else throw "sum: every set of `L` must have the identifiers of `P`, in order"
        else throw "sum: every set of `L` must have the factors of `P`"
      else throw s!"sum: the sets differ in dimension, {d.n} and {e.n}"
    let R := d.pZ.sum (m := ls.size) (fun i => (ls[i]).1) (fun i => (ls[i]).2)
    pure [("P", printPolyZonotopeIds dops.showExact (aux_construct R).materialise d.id)])
  -- CORALean's `restructure` (CORA.cpp's): the independent part boxed, made dependent
  | "restructure" => some (do
    checkFields op req ["P"]
    let d ← aux_parse dops (← field req "P")
    let R := d.pZ.restructure
    let top := d.id.foldl max 0
    let ids := d.id ++ (Array.range (R.p - d.pZ.p)).map fun j => top + 1 + j
    if ids.size ≠ R.p then throw "restructure: the factors do not match (internal)"
    pure [("P", printPolyZonotopeIds dops.showExact R.materialise ids)])
  -- the derivative along the factor `id`
  | "jacobian" => some (do
    checkFields op req ["P", "factor"]
    let d ← aux_parse dops (← field req "P")
    let id ← natField req "factor"
    match d.id.findIdx? (· == id) with
    | some r =>
      if h : r < d.pZ.p then
        pure [("P", printPolyZonotopeIds dops.showExact (d.pZ.jacobian ⟨r, h⟩).materialise d.id)]
      else throw "jacobian: the identifiers do not match the factors (internal)"
    | none => throw s!"jacobian: {id} is not an identifier of the set")
  -- the segments between two points of the sets, the factors side by side and `t` last
  | "linComb" => some (do
    checkFields op req ["P", "Q"]
    let d ← aux_parse dops (← field req "P")
    let e ← aux_parse dops (← field req "Q")
    if h : e.n = d.n then
      let Q : PolyZonotope (Vec 𝕋 d.n) := h ▸ e.pZ
      let R := d.pZ.linComb Q
      pure [("P", printPolyZonotopeIds dops.showExact R.materialise
        ((Array.range R.p).map (· + 1)))]
    else throw s!"linComb: the sets differ in dimension, {d.n} and {e.n}")
  | "convHull" => some (do
    checkFields op req ["P", "Q"]
    let d ← aux_parse dops (← field req "P")
    let e ← aux_parse dops (← field req "Q")
    if h : e.n = d.n then
      let Q : PolyZonotope (Vec 𝕋 d.n) := h ▸ e.pZ
      let R := d.pZ.convHull Q
      pure [("P", printPolyZonotopeIds dops.showExact R.materialise
        ((Array.range R.p).map (· + 1)))]
    else throw s!"convHull: the sets differ in dimension, {d.n} and {e.n}")
  -- the factors `id` at the values `val`, one after the other, then the constructor
  | "getSubset" => some (do
    checkFields op req ["P", "ids", "val"]
    let d ← aux_parse dops (← field req "P")
    let ids ← natArrField req "ids"
    aux_known d.id ids op
    let ⟨m, v⟩ ← parseVecDyn dops.readExact (← field req "val")
    if m < ids.size then throw "getSubset: `val` needs one value per identifier"
    let (R, kept) := aux_merged (aux_subsets d.pZ d.id ((ids.toList.zip (List.ofFn v)))) d.id
    pure [("P", printPolyZonotopeIds dops.showExact R.materialise kept)])
  -- `resolve`: the factors in ascending order of their identifier
  | "resolve" => some (do
    checkFields op req ["P", "ids", "x"]
    let d ← aux_parse dops (← field req "P")
    let ids ← match fieldOpt req "ids" with
      | some _ => natArrField req "ids"
      | none => pure d.id
    aux_known d.id ids op
    if ids.toList.eraseDups.length ≠ ids.size then throw "resolve: invalid ids"
    let ⟨m, v⟩ ← parseVecDyn dops.readExact (← field req "x")
    if m ≠ ids.size then throw "resolve: the length of id should match the length of x"
    let pairs := (ids.toList.zip (List.ofFn v)).toArray.qsort (fun a b => a.1 < b.1) |>.toList
    let (R, kept) := aux_merged (aux_subsets d.pZ d.id pairs) d.id
    pure [("P", printPolyZonotopeIds dops.showExact R.materialise kept)])
  -- the product of two matrix-valued sets, the matrices stored column by column
  | "matMap" => some (do
    checkFields op req ["P", "Q", "n", "k", "m"]
    -- the matrices are `n × k` and `k × m`, each stored column by column
    let n ← natField req "n"
    let k ← natField req "k"
    let m ← natField req "m"
    let A ← parsePolyZonotopeFixed dops.readExact (k * n) (← field req "P")
    let B ← parsePolyZonotopeFixed dops.readExact (m * k) (← field req "Q")
    let (R, ids) ← aux_matMap n k m A B (← field req "P") (← field req "Q")
    pure [("P", printPolyZonotopeIds dops.showExact R.materialise ids)])
  -- the cubic map of the set with its independent part made dependent
  | "cubMap" => some (do
    checkFields op req ["P", "T"]
    let d ← aux_parse dops (← field req "P")
    let ⟨_, T⟩ ← parseTensor dops.readExact d.n (← field req "T")
    let R := PolyZonotope.cubMap T d.pZ
    pure [("P", printPolyZonotopeIds dops.showExact R.materialise
      (d.id ++ aux_above d.id (R.p - d.pZ.p)))])
  -- the generators grouped by the exponents of the factors `ids`, each group on a new factor
  | "partZonotope" => some (do
    checkFields op req ["P", "ids"]
    let d ← aux_parse dops (← field req "P")
    let ids ← natArrField req "ids"
    aux_known d.id ids op
    let R := d.pZ.partZonotope (aux_factors d.pZ d.id ids)
    pure [("P", printPolyZonotopeIds dops.showExact R.materialise
      (d.id ++ aux_above d.id (R.p - d.pZ.p)))])
  -- the small generators boxed, as CORA's `outerApprox`
  | "outerApprox" => some (do
    checkFields op req ["P", "tol", "ids"]
    let d ← aux_parse dops (← field req "P")
    let tol ← dops.readExact "tol" (← scalarField req "tol")
    let ids ← natArrField req "ids"
    let R := d.pZ.outerApprox tol (aux_factors d.pZ d.id ids)
    pure [("P", printPolyZonotopeIds dops.showExact R.materialise d.id)])
  | _ => none

end CORALean.Oracle


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
