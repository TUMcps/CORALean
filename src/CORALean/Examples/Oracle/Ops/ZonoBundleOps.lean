import CORALean.ContSet.ContSet.Operations.Enclose
import CORALean.ContSet.Conversion.Float.Operations.Basic
import CORALean.ContSet.Conversion.Float.Operations.ZonoBundle_to_ConZonotope
import CORALean.ContSet.Conversion.Float.Operations.ZonoBundle_to_Zonotope
import CORALean.ContSet.ZonoBundle.Float.Instances
import CORALean.ContSet.ZonoBundle.Float.Operations.Basic
import CORALean.ContSet.ZonoBundle.Float.Operations.BoundDotLP
import CORALean.ContSet.ZonoBundle.Float.Operations.CartProd
import CORALean.ContSet.ZonoBundle.Float.Operations.Enlarge
import CORALean.ContSet.ZonoBundle.Float.Operations.Intersection
import CORALean.ContSet.ZonoBundle.Float.Operations.IntervalAll
import CORALean.ContSet.ZonoBundle.Float.Operations.Isequal
import CORALean.ContSet.ZonoBundle.Float.Operations.LinComb
import CORALean.ContSet.ZonoBundle.Float.Operations.Mtimes
import CORALean.ContSet.ZonoBundle.Float.Operations.Plus
import CORALean.ContSet.ZonoBundle.Float.Operations.Project
import CORALean.ContSet.ZonoBundle.Float.Operations.QuadMap
import CORALean.ContSet.ZonoBundle.Float.Operations.Reduce
import CORALean.ContSet.ZonoBundle.Float.Operations.ReduceCombined
import CORALean.ContSet.ZonoBundle.Float.Operations.Reindex
import CORALean.ContSet.ZonoBundle.Float.Operations.Replace
import CORALean.ContSet.ZonoBundle.Float.Operations.RepresentsaEmptySet
import CORALean.ContSet.ZonoBundle.Float.Operations.Shrink
import CORALean.Examples.Oracle.Ops.SetCodec
import CORALean.Specification.Instances

/-!
# The zonotope-bundle ops: CORA's `zonoBundle` methods

Thin adapters over the float definitions `references/coverage/contSet/zonoBundle.md` links.
Operands are `zB`, `zB2` (`{"Zs":[zonotope, ...]}`, at least one member for the ops that need
one); a set result is `zB`, a zonotope `Z`, a constrained zonotope `cZ`, a box `I`, a Boolean or a
bound `value`. Indices are 0-based; a field an op does not list is refused by name. Not served:
`contains`, `isFullDim` (a right inverse per member), `encloseTight`, `split` (matrices CORA does
not take), `vertices` (CORALean's is one member's), the classes without a wire format
(`conPolyZono`, `spectraShadow`) and the constructor `zonoBundle`.

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

private def aux_set (dops : DtypeOps 𝕋) (name : String) {n : Nat} (zB : ZonoBundle (Vec 𝕋 n)) :
    String × Json :=
  (name, printZonoBundle dops.showExact zB)

/-- Two bundles of one dimension in. -/
private def aux_pair (dops : DtypeOps 𝕋) (req : Json) :
    Except String (Σ n : Nat, ZonoBundle (Vec 𝕋 n) × ZonoBundle (Vec 𝕋 n)) := do
  let d ← parseZonoBundle dops.readExact (← field req "zB")
  let b ← parseZonoBundleFixed dops.readExact d.n (← field req "zB2")
  pure ⟨d.n, d.zB, b⟩

private def aux_binary (op : String) (dops : DtypeOps 𝕋) (req : Json)
    (f : {n : Nat} → ZonoBundle (Vec 𝕋 n) → ZonoBundle (Vec 𝕋 n) →
      ZonoBundle (Vec 𝕋 n)) : Resp := do
  checkFields op req ["zB", "zB2"]
  let ⟨_, a, b⟩ ← aux_pair dops req
  pure [aux_set dops "zB" (f a b)]

/-- The bundle has a member, which the ops that read one need. -/
private def aux_nonempty {n : Nat} (op : String) (zB : ZonoBundle (Vec 𝕋 n)) :
    Except String (PLift (0 < zB.k)) :=
  if h : 0 < zB.k then pure ⟨h⟩ else throw s!"{op}: the bundle has no member"


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `zonoBundle.enclose`: CORA's `enclose(zB, M, zB2)`, `ContSet.enclose` at the float instances. -/
def handleBundleEnclose (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "enclose" req ["zB", "M", "zB2"]
  let d ← parseZonoBundle dops.readExact (← field req "zB")
  let b ← parseZonoBundleFixed dops.readExact d.n (← field req "zB2")
  let ⟨r, M⟩ ← parseMatColsFixed dops.readExact d.n (← field req "M")
  if h : r = d.n then
    pure [aux_set dops "zB" (ContSet.enclose (𝕋 := 𝕋) (S := 𝒵ℬ[𝕋]) d.zB
      (h ▸ M) b)]
  else throw s!"enclose: `M` has {r} rows, expected {d.n}"

/-- `zonoBundle.supportFunc`: the upper bound of `dir · x`, `ZonoBundle.boundDotLP`. -/
def handleBundleSupportFunc (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "supportFunc" req ["zB", "dir", "type"]
  checkStrOption "supportFunc" req "type" "upper"
  let d ← parseZonoBundle dops.readExact (← field req "zB")
  let ⟨hk⟩ ← aux_nonempty "supportFunc" d.zB
  let a ← parseVecFixed dops.readExact d.n (← field req "dir")
  valueScalar dops.showExact (d.zB.boundDotLP hk (c := rowFunctional a) a fun _ => rfl).val

/-- `zonoBundle.replace`: member `index` replaced by `Z`. -/
def handleBundleReplace (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "replace" req ["zB", "index", "Z"]
  let d ← parseZonoBundle dops.readExact (← field req "zB")
  let i ← indexField req "index" d.zB.k
  let Z ← parseZonotopeFixed dops.readExact d.n (← field req "Z")
  pure [aux_set dops "zB" (ZonoBundle.replace d.zB i Z)]

/-- Every op of this file, without the `zonoBundle.` prefix. -/
def zonoBundleOpNames : List String :=
  [ "and", "cartProd", "conZonotope", "empty", "enclose", "enlarge", "interval", "isBounded",
    "isIntersecting", "isequal", "lift", "mtimes", "origin", "plus", "project", "quadMap",
    "reduce", "reduceCombined", "replace", "representsa", "shrink", "supportFunc", "zonotope",
    "convHull", "polytope" ]

/-- `op` of `zonoBundle.`, run; `none` for a name this file does not serve. -/
@[noinline, nospecialize]
def handleZonoBundleOp (dops : DtypeOps 𝕋) (op : String) (req : Json) : Option Resp :=
  match op with
  | "and" => some (aux_binary op dops req fun a b => ZonoBundle.intersection a b)
  | "cartProd" => some (do
      checkFields op req ["zB", "zB2"]
      let a ← parseZonoBundle dops.readExact (← field req "zB")
      let b ← parseZonoBundle dops.readExact (← field req "zB2")
      pure [aux_set dops "zB" (ZonoBundle.cartProd a.zB b.zB)])
  | "convHull" => some (aux_binary op dops req fun a b => ZonoBundle.linComb a b)
  | "conZonotope" => some (do
      checkFields op req ["zB"]
      let d ← parseZonoBundle dops.readExact (← field req "zB")
      let ⟨hk⟩ ← aux_nonempty op d.zB
      pure [("cZ", printConZonotope dops.showExact (ZonoBundle.conZonotopeAll d.zB hk))])
  -- the arms from `empty` on
  | "empty" => some (do
      checkFields op req ["n"]
      let n ← natField req "n"
      if hn : 0 < n then pure [aux_set dops "zB" (ZonoBundle.empty (𝕋 := 𝕋) n hn)]
      else throw "empty: `n` must be positive, CORALean's empty bundle is two points of R^n")
  | "enclose" => some (handleBundleEnclose dops req)
  | "enlarge" => some (do
      checkFields op req ["zB", "factor"]
      let d ← parseZonoBundle dops.readExact (← field req "zB")
      let f ← parseVecFixed dops.readExact d.n (← field req "factor")
      pure [aux_set dops "zB" (ZonoBundle.enlarge d.zB f)])
  -- the arms from `interval` on
  | "interval" => some (do
      checkFields op req ["zB"]
      let d ← parseZonoBundle dops.readExact (← field req "zB")
      let ⟨hk⟩ ← aux_nonempty op d.zB
      pure [("I", printIntervalVec dops.showExact (ZonoBundle.intervalAll d.zB hk))])
  | "isBounded" => some (do
      checkFields op req ["zB", "tol"]
      checkTol op req
      valueBool true)
  | "isIntersecting" => some (do
      checkFields op req ["zB", "zB2", "tol", "type"]
      checkTol op req
      let ⟨_, a, b⟩ ← aux_pair dops req
      pure [("disjoint", Json.bool (IsDisjoint.isDisjoint a b))])
  -- the arms from `isequal` on
  | "isequal" => some (do
      checkFields op req ["zB", "zB2", "tol"]
      checkTol op req
      let ⟨_, a, b⟩ ← aux_pair dops req
      valueBool (ZonoBundle.isequal a b))
  | "lift" => some (do
      checkFields op req ["zB", "N", "dims"]
      let d ← parseZonoBundle dops.readExact (← field req "zB")
      let e ← liftPerm req d.n
      pure [aux_set dops "zB" (ZonoBundle.reindex e.symm d.zB)])
  -- the arms from `mtimes` on
  | "mtimes" => some (do
      checkFields op req ["zB", "M"]
      let d ← parseZonoBundle dops.readExact (← field req "zB")
      let ⟨_, M⟩ ← parseMatColsFixed dops.readExact d.n (← field req "M")
      pure [aux_set dops "zB" (ZonoBundle.mtimes M d.zB)])
  | "origin" => some (do
      checkFields op req ["n"]
      pure [aux_set dops "zB" (ZonoBundle.origin (𝕋 := 𝕋) (← natField req "n"))])
  | "plus" => some (aux_binary op dops req fun a b => ZonoBundle.plus a b)
  | "project" => some (do
      checkFields op req ["zB", "dims"]
      let d ← parseZonoBundle dops.readExact (← field req "zB")
      let ⟨_, dims⟩ ← indexArrField req "dims" d.n
      pure [aux_set dops "zB" (ZonoBundle.project d.zB dims)])
  -- the arms from `quadMap` on
  | "quadMap" => some (do
      checkFields op req ["zB", "Q"]
      let d ← parseZonoBundle dops.readExact (← field req "zB")
      let ⟨_, Q⟩ ← parseSquareList dops.readExact d.n (← field req "Q")
      pure [aux_set dops "zB" (ZonoBundle.quadMap Q d.zB)])
  | "reduce" => some (do
      checkFields op req ["zB", "order", "method"]
      checkStrOption op req "method" "girard"
      let d ← parseZonoBundle dops.readExact (← field req "zB")
      pure [aux_set dops "zB" (ZonoBundle.reduce d.zB (← natField req "order"))])
  -- the arms from `reduceCombined` on
  | "reduceCombined" => some (do
      checkFields op req ["zB", "method"]
      checkStrOption op req "method" "methC"
      let d ← parseZonoBundle dops.readExact (← field req "zB")
      let ⟨hk⟩ ← aux_nonempty op d.zB
      pure [("Z", printZonotope dops.showExact (ZonoBundle.reduceCombined d.zB hk))])
  | "replace" => some (handleBundleReplace dops req)
  | "representsa" => some (do
      checkFields op req ["zB", "type", "tol"]
      checkTol op req
      checkStrOption op req "type" "emptySet"
      let d ← parseZonoBundle dops.readExact (← field req "zB")
      valueBool (ZonoBundle.representsa_emptySet d.zB))
  -- the arms from `shrink` on
  | "shrink" => some (do
      checkFields op req ["zB"]
      let d ← parseZonoBundle dops.readExact (← field req "zB")
      let ⟨hk⟩ ← aux_nonempty op d.zB
      pure [aux_set dops "zB" (ZonoBundle.shrink d.zB hk)])
  | "supportFunc" => some (handleBundleSupportFunc dops req)
  -- the facets of the members, intersected
  | "polytope" => some (do
      checkFields op req ["zB", "p"]
      let d ← parseZonoBundle dops.readExact (← field req "zB")
      match hn : d.n with
      | 0 => throw "polytope: CORA's facet enumeration needs at least one dimension"
      | m + 1 =>
        let zB : ZonoBundle (Vec 𝕋 (m + 1)) := cast (by rw [hn]) d.zB
        pure [("P", printHPolytope dops.showExact
          (ZonoBundle.hPolytopeAll (← natField req "p") zB))])
  | "zonotope" => some (do
      checkFields op req ["zB"]
      let d ← parseZonoBundle dops.readExact (← field req "zB")
      let ⟨hk⟩ ← aux_nonempty op d.zB
      let i := ZonoBundle.minVolIdx d.zB hk
      pure [("Z", printZonotope dops.showExact (ZonoBundle.zonotope d.zB i))])
  | _ => none

end CORALean.Oracle


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
