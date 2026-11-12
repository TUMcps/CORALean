import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_HPolytope
import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_VPolytope
import CORALean.ContSet.HPolytope.Real.Operations.RowLin
import CORALean.ContSet.Zonotope.Float.Operations.Abs
import CORALean.ContSet.Zonotope.Float.Operations.And
import CORALean.ContSet.ContSet.Operations.EnlargeScalar
import CORALean.ContSet.ContSet.Operations.MinusScalar
import CORALean.ContSet.ContSet.Operations.ProjectOnHyperplaneFloat
import CORALean.ContSet.Zonotope.Float.Operations.Basic
import CORALean.ContSet.Zonotope.Float.Operations.BoundaryPoint
import CORALean.ContSet.Zonotope.Float.Operations.CartProd
import CORALean.ContSet.Zonotope.Float.Operations.CompactZeros
import CORALean.ContSet.Zonotope.Float.Operations.ConstrSat
import CORALean.ContSet.Zonotope.Float.Operations.ContainsZonotope
import CORALean.ContSet.Zonotope.Float.Operations.CubMap
import CORALean.ContSet.Zonotope.Float.Operations.DominantDirections
import CORALean.ContSet.Zonotope.Float.Operations.EncloseMany
import CORALean.ContSet.Zonotope.Float.Operations.EnclosePointsStursberg
import CORALean.ContSet.Zonotope.Float.Operations.ExactPlus
import CORALean.ContSet.Zonotope.Float.Operations.FilterOut
import CORALean.ContSet.Zonotope.Float.Operations.GeneratorLength
import CORALean.ContSet.Zonotope.Float.Operations.IntersectStrip
import CORALean.ContSet.Zonotope.Float.Operations.IsFullDim
import CORALean.ContSet.Zonotope.Float.Operations.Isequal
import CORALean.ContSet.Zonotope.Float.Operations.LinComb
import CORALean.ContSet.Zonotope.Float.Operations.Minnorm
import CORALean.ContSet.Zonotope.Float.Operations.NormSq
import CORALean.ContSet.Zonotope.Float.Operations.Polygon
import CORALean.ContSet.Zonotope.Float.Operations.Project
import CORALean.ContSet.Zonotope.Float.Operations.ProjectHighDim
import CORALean.ContSet.Zonotope.Float.Operations.QuadMap
import CORALean.ContSet.Zonotope.Float.Operations.QuadMapTri
import CORALean.ContSet.Zonotope.Float.Operations.Radius
import CORALean.ContSet.Zonotope.Float.Operations.Reindex
import CORALean.ContSet.Zonotope.Float.Operations.RepresentsaOrigin
import CORALean.ContSet.Zonotope.Float.Operations.RepresentsaPoint
import CORALean.ContSet.Zonotope.Float.Operations.Rotate
import CORALean.ContSet.Zonotope.Float.Operations.Split
import CORALean.ContSet.Zonotope.Float.Operations.SplitFirstGen
import CORALean.ContSet.Zonotope.Float.Operations.MinkDiffAligned
import CORALean.ContSet.Zonotope.Float.Operations.MinkDiffRep
import CORALean.ContSet.Zonotope.Float.Operations.MinkDiffStretch
import CORALean.ContSet.Zonotope.Float.Operations.MinkDiffStretchInner
import CORALean.ContSet.Zonotope.Float.Operations.ReduceUnderApprox
import CORALean.ContSet.Zonotope.Float.Operations.SplitLongestGen
import CORALean.ContSet.Zonotope.Float.Operations.TensorMultiplicationZono
import CORALean.ContSet.Zonotope.Float.Operations.Underapproximate
import CORALean.ContSet.Zonotope.Float.Operations.AbsorbRounding
import CORALean.ContSet.Zonotope.Float.Operations.ZonotopeNorm
import CORALean.Examples.Oracle.Ops.OpCommon
import CORALean.Specification.Instances

/-!
# The zonotope ops: CORA's `zonotope` methods

Thin adapters over the float definitions `references/coverage/contSet/zonotope.md` links. Operands
are `Z`, `Z2` (`{"c","G","E"}`); a set result is `Z` (`I`, a box), anything else `value`; indices
are 0-based; a field an op does not list is refused by name. `contains` and `isFullDim` use the
library's own right inverse `Zonotope.rightInvCandidate`, as do `underapproximate` and `contains`.
`tensorMultiplication` and `tensorMultiplication_zono` read CORA's `options.list` as `perm`, `map`
and `C`. `minkDiff` and `reduceUnderApprox` take the certificate as fields (README). Not served:
`volume`, `rank` and `dH2box` (no float definition).

## Inputs
* `dops` – dtype operations
* `req` – request

## Output
* response fields or an error message
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-November-2026
-- Last update:   03-November-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Oracle

open CORALean CORALean.Float
open Lean (Json)

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A response carrying the zonotope `Z` under `name`. -/
private def aux_zField (dops : DtypeOps 𝕋) (name : String) {n : Nat} (Z : Zonotope (Vec 𝕋 n)) :
    String × Json :=
  (name, printZonotope dops.showExact Z)

/-- The scalar `x` as the response `value`. -/
private def aux_value (dops : DtypeOps 𝕋) (x : 𝕋) : Resp :=
  pure [("value", Json.str (dops.showExact x))]

/-- The Boolean `b` as the response `value`. -/
private def aux_bool (b : Bool) : Resp := pure [("value", Json.bool b)]

/-- A zonotope in, a zonotope out. -/
private def aux_unary (op : String) (dops : DtypeOps 𝕋) (req : Json) (extra : List String)
    (f : {n : Nat} → Zonotope (Vec 𝕋 n) → Zonotope (Vec 𝕋 n)) : Resp := do
  checkFields op req ("Z" :: extra)
  let dz ← parseZonotope dops.readExact (← field req "Z")
  pure [aux_zField dops "Z" (f dz.Z)]

/-- Two zonotopes of one dimension in. -/
private def aux_pair (dops : DtypeOps 𝕋) (req : Json) :
    Except String (Σ n : Nat, Zonotope (Vec 𝕋 n) × Zonotope (Vec 𝕋 n)) := do
  let dz ← parseZonotope dops.readExact (← field req "Z")
  let Z2 ← parseZonotopeFixed dops.readExact dz.n (← field req "Z2")
  pure ⟨dz.n, dz.Z, Z2⟩

/-- Two zonotopes in, a zonotope out. -/
private def aux_binary (op : String) (dops : DtypeOps 𝕋) (req : Json)
    (f : {n : Nat} → Zonotope (Vec 𝕋 n) → Zonotope (Vec 𝕋 n) → Zonotope (Vec 𝕋 n)) : Resp := do
  checkFields op req ["Z", "Z2"]
  let ⟨_, Z, Z2⟩ ← aux_pair dops req
  pure [aux_zField dops "Z" (f Z Z2)]

/-- A zonotope in, a Boolean out. -/
private def aux_test (op : String) (dops : DtypeOps 𝕋) (req : Json) (extra : List String)
    (f : {n : Nat} → Zonotope (Vec 𝕋 n) → Bool) : Resp := do
  checkFields op req ("Z" :: "tol" :: extra)
  checkTol op req
  let dz ← parseZonotope dops.readExact (← field req "Z")
  aux_bool (f dz.Z)

/-- `m` cells `Zs` of one dimension `n`, read from the array field `name`. -/
private def aux_cells (dops : DtypeOps 𝕋) (req : Json) (name : String) (n : Nat) :
    Except String (Array (Zonotope (Vec 𝕋 n))) := do
  (← arrField req name).mapM (parseZonotopeFixed dops.readExact n)

/-- A third-order tensor `T`, `m` blocks of `n` matrices of `n × n`. -/
private def aux_tensor (dops : DtypeOps 𝕋) (n : Nat) (j : Json) :
    Except String (Σ m : Nat, Fin m → Fin n → Mat 𝕋 n n) := do
  let rows ← (← j.getArr?).mapM fun row => do
    (← row.getArr?).mapM fun mj => do
      let ⟨r, M⟩ ← parseMatColsFixed dops.readExact n mj
      if h : r = n then pure (h ▸ M) else throw s!"`T`: expected {n}×{n} matrices"
  if h : ∀ (i : Fin rows.size), (rows[i]).size = n then
    pure ⟨rows.size, fun i k => (rows[i]).getD k.val (fun _ _ => (FloatOps.zero : 𝕋))⟩
  else throw s!"`T`: every block must hold {n} matrices"

/-- A third-order tensor `M = {M₁, …, Mₙ}`: `n` blocks, one per output coordinate, each of `n`
matrices `n × n`, entry `M{i}(j, k, l)` the entry `(k, l)` of the `j`-th matrix of block `i`. -/
private def aux_tensor3 (dops : DtypeOps 𝕋) (n : Nat) (j : Json) :
    Except String (Tensor3 𝕋 n) := do
  let ⟨m, T⟩ ← aux_tensor dops n j
  if h : m = n then pure fun i a b c => T (Fin.cast h.symm i) a b c
  else throw s!"`M`: expected {n} blocks, got {m}"

/-- CORA's `options.list` over `k` generators: `perm` (rows of three 0-based generator indices),
`map` (the combination of each permutation, 0-based) and `C`, the number of combinations. -/
private def aux_tensorLists (req : Json) (k : Nat) :
    Except String (Real.Zonotope.TensorLists k) := do
  let perm ← arrField req "perm"
  let map ← arrField req "map"
  let C ← natField req "C"
  -- an index below its bound, 0-based
  let idx (what : String) (bound : Nat) (v : Json) : Except String (Fin bound) := do
    let i ← match v.getNat? with
      | .ok i => pure i
      | .error _ => throw s!"`{what}`: indices are nonnegative integers"
    if h : i < bound then pure ⟨i, h⟩
    else throw s!"`{what}`: index {i} is out of range, the bound is {bound} (indices are 0-based)"
  -- each permutation row is three generator indices
  let perm ← perm.mapM fun row => do
    let r ← row.getArr?
    if h : r.size = 3 then
      pure (← idx "perm" k r[0], ← idx "perm" k r[1], ← idx "perm" k r[2])
    else throw "`perm`: every row holds three generator indices"
  let map ← map.mapM (idx "map" C)
  if h : perm.size = map.size then
    pure ⟨perm.size, C, fun p q => ![(perm[p]).1, (perm[p]).2.1, (perm[p]).2.2] q,
      fun p => map[p.val]'(h ▸ p.isLt)⟩
  else throw s!"`perm` has {perm.size} rows but `map` {map.size} entries"

/-- The upper bound of `dir · x` over the zonotope, the library's `boundDot` at the row functional
of `dir`. -/
private def aux_bound {n : Nat} (Z : Zonotope (Vec 𝕋 n)) (a : Vec 𝕋 n) : 𝕋 :=
  let c : Vec ℝ n →ₗ[ℝ] ℝ := Real.HPolytope.rowLin (toRealMat (fun (_ : Fin 1) => a)) 0
  (Z.boundDot (c := c) a fun _ => rfl).val

/-- The cap on `2 ^ h` corners that `vertices` enumerates. -/
private def aux_maxGenerators : Nat := 20


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `zonotope.contains`: `Z` (the container) certified to contain `Z2`. -/
def handleZonoContains (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "contains" req ["Z", "Z2", "tol"]
  checkTol "contains" req
  let ⟨_, Z, Z2⟩ ← aux_pair dops req
  -- the candidate tabulated once, as in `handleZonoIsFullDim`
  let tab := tableOf (Zonotope.rightInvCandidate fun i k => Z.G k i)
  let H : Mat 𝕋 Z.h _ := fun j i => tableGet FloatOps.zero tab j i
  pure [("contains", Json.bool (Zonotope.containsZonotope Z Z2 H))]

/-- `zonotope.isFullDim`: `Zonotope.isFullDim`, that is `Zonotope.isFullDimWith` at the library's
right inverse `Zonotope.rightInvCandidate`, here tabulated once: the candidate is a function whose
every entry would otherwise redo the Gram inverse, which made a 30-generator test take a minute. -/
def handleZonoIsFullDim (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "isFullDim" req ["Z", "tol"]
  checkTol "isFullDim" req
  let dz ← parseZonotope dops.readExact (← field req "Z")
  let tab := tableOf (Zonotope.rightInvCandidate fun i k => dz.Z.G k i)
  aux_bool (Zonotope.isFullDimWith dz.Z fun j i => tableGet FloatOps.zero tab j i)

/-- `zonotope.isIntersecting`: `disjoint = true` certifies that `Z` and `Z2` share no point. -/
def handleZonoIsIntersecting (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "isIntersecting" req ["Z", "Z2", "tol"]
  checkTol "isIntersecting" req
  let ⟨n, Z, Z2⟩ ← aux_pair dops req
  letI : IsDisjoint (Zonotope (Vec 𝕋 n)) (Zonotope (Vec 𝕋 n)) :=
    isDisjointBoxBoxOuter (T := 𝒵[𝕋]) (S := 𝒵[𝕋])
  pure [("disjoint", Json.bool (IsDisjoint.isDisjoint Z Z2))]

/-- `zonotope.representsa`: `type` one of `point`, `origin`. -/
def handleZonoRepresentsa (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "representsa" req ["Z", "type", "tol"]
  checkTol "representsa" req
  let dz ← parseZonotope dops.readExact (← field req "Z")
  match ← strField req "type" with
  | "point" => aux_bool (Zonotope.representsa_point dz.Z)
  -- constructors and projections
  | "origin" => aux_bool (Zonotope.representsa_origin dz.Z)
  | t => throw s!"representsa: `type` must be point or origin, not `{t}`"

/-- `zonotope.supportFunc`: the upper bound of `dir · x`, `Zonotope.boundDot`. -/
def handleZonoSupportFunc (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "supportFunc" req ["Z", "dir", "type"]
  let ty := (fieldOpt req "type").bind (·.getStr?.toOption)
  unless ty.isNone || ty = some "upper" do
    throw "supportFunc: `type` must be `upper`, the float definition bounds from above only"
  let dz ← parseZonotope dops.readExact (← field req "Z")
  let a ← parseVecFixed dops.readExact dz.n (← field req "dir")
  aux_value dops (aux_bound dz.Z a)

/-- `zonotope.constrSat`: `C z ≤ d` certified for every point, `Zonotope.constrSat`. -/
def handleZonoConstrSat (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "constrSat" req ["Z", "C", "d"]
  let dz ← parseZonotope dops.readExact (← field req "Z")
  let ⟨m, C⟩ ← parseMatColsFixed dops.readExact dz.n (← field req "C")
  let d ← parseVecFixed dops.readExact m (← field req "d")
  aux_bool (Zonotope.constrSat dz.Z C d)

/-- `zonotope.project`: coordinates `dims`. -/
def handleZonoProject (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "project" req ["Z", "dims"]
  let dz ← parseZonotope dops.readExact (← field req "Z")
  let ⟨_, d⟩ ← indexArrField req "dims" dz.n
  pure [aux_zField dops "Z" (Zonotope.project dz.Z d)]

/-- `zonotope.projectHighDim`: coordinate `k` written at `dims[k]` of `N` dimensions. -/
def handleZonoProjectHighDim (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "projectHighDim" req ["Z", "N", "dims"]
  let dz ← parseZonotope dops.readExact (← field req "Z")
  let N ← natField req "N"
  let ⟨m, d⟩ ← indexArrField req "dims" N
  if h : m = dz.n then
    pure [aux_zField dops "Z" (Zonotope.projectHighDim_ (h ▸ dz.Z) N d)]
  else throw s!"projectHighDim: `dims` has {m} entries, the dimension of `Z` is {dz.n}"

/-- `zonotope.lift`: CORA's `lift_` is `project` when `dims` has `N` entries, a permutation of
the coordinates, which is `Zonotope.reindex`; any other `N` is refused, as CORA does. -/
def handleZonoLift (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "lift" req ["Z", "N", "dims"]
  let dz ← parseZonotope dops.readExact (← field req "Z")
  let N ← natField req "N"
  let ⟨m, d⟩ ← indexArrField req "dims" N
  if hN : N = dz.n then
    if hm : m = N then
      let f : Fin N → Fin N := fun i => d (Fin.cast hm.symm i)
      if hinj : Function.Injective f then
        have hsurj : ∀ j, ∃ i, f i = j := Finite.injective_iff_surjective.mp hinj
        let e : Fin N ≃ Fin N :=
          { toFun := f
            invFun := fun j => Fin.find (fun i => f i = j) (hsurj j)
            left_inv := fun i => hinj (Fin.find_spec (p := fun i' => f i' = f i) (hsurj (f i)))
            right_inv := fun j => Fin.find_spec (p := fun i => f i = j) (hsurj j) }
        pure [aux_zField dops "Z" (Zonotope.reindex e.symm (hN ▸ dz.Z))]
      else throw "lift: `dims` must be a permutation, it repeats a coordinate"
    else throw s!"lift: `dims` has {m} entries but N = {N}, CORA's lift_ is not defined"
  else throw s!"lift: N = {N} differs from the dimension {dz.n}, CORA's lift_ is not defined"

/-- `zonotope.split`: halves along generator `gen`. -/
def handleZonoSplit (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "split" req ["Z", "gen"]
  let dz ← parseZonotope dops.readExact (← field req "Z")
  let j ← indexField req "gen" dz.Z.h
  let (Z1, Z2) := Zonotope.split dz.Z j
  pure [aux_zField dops "Z1" Z1, aux_zField dops "Z2" Z2]

/-- `zonotope.splitFirstGen`, `zonotope.splitLongestGen`: halves along a chosen generator. -/
def handleZonoSplitBy (op : String) (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields op req ["Z"]
  let dz ← parseZonotope dops.readExact (← field req "Z")
  let (Z1, Z2) := if op = "splitFirstGen" then Zonotope.splitFirstGen dz.Z
    else Zonotope.splitLongestGen dz.Z
  pure [aux_zField dops "Z1" Z1, aux_zField dops "Z2" Z2]

/-- `zonotope.quadMap`: `Q` an array of `n × n` matrices. -/
def handleZonoQuadMap (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "quadMap" req ["Z", "Q"]
  let dz ← parseZonotope dops.readExact (← field req "Z")
  let qs ← (← arrField req "Q").mapM fun j => do
    let ⟨r, M⟩ ← parseMatColsFixed dops.readExact dz.n j
    if h : r = dz.n then pure (h ▸ M) else throw s!"quadMap: expected {dz.n}×{dz.n} matrices"
  pure [aux_zField dops "Z" (Zonotope.quadMap (m := qs.size) (fun k => qs[k]) dz.Z)]

/-- `zonotope.quadMapTri`: `Q` as for `quadMap`; CORA's generators, `N + N(N + 1)/2` of them. -/
def handleZonoQuadMapTri (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "quadMapTri" req ["Z", "Q"]
  let dz ← parseZonotope dops.readExact (← field req "Z")
  let qs ← (← arrField req "Q").mapM fun j => do
    let ⟨r, M⟩ ← parseMatColsFixed dops.readExact dz.n j
    if h : r = dz.n then pure (h ▸ M) else throw s!"quadMapTri: expected {dz.n}×{dz.n} matrices"
  pure [aux_zField dops "Z" (Zonotope.quadMapTri (m := qs.size) (fun k => qs[k]) dz.Z)]

/-- `zonotope.cubMap`: `T` an array of `m` arrays of `n` matrices of `n × n`. -/
def handleZonoCubMap (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "cubMap" req ["Z", "T"]
  let dz ← parseZonotope dops.readExact (← field req "Z")
  let ⟨_, T⟩ ← aux_tensor dops dz.n (← field req "T")
  pure [aux_zField dops "Z" (Zonotope.cubMap T dz.Z)]

/-- `zonotope.cartProd`: the product of two zonotopes. -/
def handleZonoCartProd (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "cartProd" req ["Z", "Z2"]
  let a ← parseZonotope dops.readExact (← field req "Z")
  let b ← parseZonotope dops.readExact (← field req "Z2")
  pure [aux_zField dops "Z" (Zonotope.cartProd a.Z b.Z)]

/-- `zonotope.exactPlus`: the sum with the first `k` generator pairs added. -/
def handleZonoExactPlus (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "exactPlus" req ["Z", "Z2", "k"]
  let ⟨_, Z, Z2⟩ ← aux_pair dops req
  pure [aux_zField dops "Z" (Zonotope.exactPlus Z Z2 (← natField req "k"))]

/-- `zonotope.intersectStrip`: the strips `|C x - y| ≤ phi` at the gain `Lambda`. -/
def handleZonoIntersectStrip (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "intersectStrip" req ["Z", "C", "phi", "y", "Lambda"]
  let dz ← parseZonotope dops.readExact (← field req "Z")
  let ⟨p, C⟩ ← parseMatColsFixed dops.readExact dz.n (← field req "C")
  let φ ← parseVecFixed dops.readExact p (← field req "phi")
  let y ← parseVecFixed dops.readExact p (← field req "y")
  let ⟨r, Λ⟩ ← parseMatColsFixed dops.readExact p (← field req "Lambda")
  if h : r = dz.n then
    pure [aux_zField dops "Z" (Zonotope.intersectStrip C φ y (h ▸ Λ) dz.Z)]
  else throw s!"intersectStrip: `Lambda` has {r} rows, the dimension of `Z` is {dz.n}"

/-- `zonotope.rotate`: the rotation by `angle` in the plane of axes `i`, `j`, `p` Newton steps. -/
def handleZonoRotate (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "rotate" req ["Z", "p", "i", "j", "angle"]
  let dz ← parseZonotope dops.readExact (← field req "Z")
  let i ← indexField req "i" dz.n
  let j ← indexField req "j" dz.n
  let angle ← dops.readExact "angle" (← scalarField req "angle")
  pure [aux_zField dops "Z" (Zonotope.rotate (← natField req "p") dz.Z i j angle)]

/-- `zonotope.radius`: a radius of a ball about the center, `k` Newton steps. -/
def handleZonoRadius (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "radius" req ["Z", "k"]
  let dz ← parseZonotope dops.readExact (← field req "Z")
  aux_value dops (Zonotope.radius (← natField req "k") dz.Z)

/-- `zonotope.generatorLength`: the Euclidean length of every generator, `k` Newton steps. -/
def handleZonoGeneratorLength (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "generatorLength" req ["Z", "k"]
  let dz ← parseZonotope dops.readExact (← field req "Z")
  let k ← natField req "k"
  pure [("value", printVec dops.showExact fun j : Fin dz.Z.h => Zonotope.generatorLength k dz.Z j)]

/-- `zonotope.minnorm`: an upper bound on the least facet offset, `null` when there is none. -/
def handleZonoMinnorm (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "minnorm" req ["Z", "p"]
  let dz ← parseZonotope dops.readExact (← field req "Z")
  let p ← natField req "p"
  match dz with
  | ⟨0, _⟩ => throw "minnorm: the zonotope must have dimension at least 1"
  | ⟨_ + 1, Z⟩ =>
    match Zonotope.minnorm p Z with
    | some x => pure [("value", Json.str (dops.showExact x))]
    | none => pure [("value", Json.null)]

/-- `zonotope.zonotopeNorm`: a lower bound on `‖p‖_Z`, `"inf"` where `p` is certified outside the
span of the generators (CORA's `Inf`). -/
def handleZonoZonotopeNorm (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "zonotopeNorm" req ["Z", "p"]
  let dz ← parseZonotope dops.readExact (← field req "Z")
  match dz with
  | ⟨0, _⟩ => throw "zonotopeNorm: the zonotope must have dimension at least 1"
  | ⟨_ + 1, Z⟩ =>
    let pt ← parseVecFixed dops.readExact _ (← field req "p")
    match Zonotope.zonotopeNorm Z pt with
    | some x => pure [("value", Json.str (dops.showExact x))]
    | none => pure [("value", Json.str "inf")]

/-- `zonotope.tensorMultiplication`: the zonotope `(0, H)` enclosing `{ M_ijkl x_j x_k x_l }`, over
the generators of `Z` with its error box made generators (`Zonotope.absorbRounding`), which the
indices of `perm` count. -/
def handleZonoTensorMultiplication (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "tensorMultiplication" req ["Z", "M", "perm", "map", "C"]
  let dz ← parseZonotope dops.readExact (← field req "Z")
  let M ← aux_tensor3 dops dz.n (← field req "M")
  let L ← aux_tensorLists req dz.Z.absorbRounding.h
  pure [aux_zField dops "Z" (Zonotope.tensorMultiplication dz.Z M L)]

/-- `zonotope.tensorMultiplication_zono`: the tensor is the matrix zonotope `M = {c, G}` over
third-order tensors, `c` a tensor and `G` an array of them. -/
def handleZonoTensorMultiplicationZono (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "tensorMultiplication_zono" req ["Z", "M", "perm", "map", "C"]
  let dz ← parseZonotope dops.readExact (← field req "Z")
  let Mj ← field req "M"
  let c ← aux_tensor3 dops dz.n (← field Mj "c")
  let G ← (← arrField Mj "G").mapM (aux_tensor3 dops dz.n)
  let z0 : Tensor3 𝕋 dz.n := fun _ _ _ _ => FloatOps.zero
  let M : Zonotope (Tensor3 𝕋 dz.n) := ⟨G.size, c, fun j => G[j], ⟨z0, z0⟩⟩
  let L ← aux_tensorLists req dz.Z.absorbRounding.h
  pure [aux_zField dops "Z" (Zonotope.tensorMultiplication_zono dz.Z M L)]

/-- The right inverse of `Z`'s generators: the request's `H` (`Z.h × n`), else the library's
`Zonotope.rightInvCandidate`, tabulated once. -/
private def aux_rightInv (dops : DtypeOps 𝕋) (req : Json) {n : Nat} (Z : Zonotope (Vec 𝕋 n)) :
    Except String (Mat 𝕋 Z.h n) := do
  match fieldOpt req "H" with
  | some hj =>
    let ⟨r, Hm⟩ ← parseMatColsFixed dops.readExact n hj
    if h : r = Z.h then pure (h ▸ Hm) else throw s!"`H` has {r} rows, `Z` has {Z.h} generators"
  | none =>
    let tab := tableOf (Zonotope.rightInvCandidate fun i k => Z.G k i)
    pure fun j i => tableGet FloatOps.zero tab j i

/-- A certified result as `Z`, `null` where the check failed. -/
private def aux_optZ (dops : DtypeOps 𝕋) {n : Nat} : Option (Zonotope (Vec 𝕋 n)) → Resp
  | some Z => pure [aux_zField dops "Z" Z]
  | none => pure [("Z", Json.null)]

/-- `minkDiff` with `method` `rep`: `Zonotope.minkDiffRep` at `M` (`Z.h × Z2.h`) and `rho`. -/
private def aux_minkDiffRep (dops : DtypeOps 𝕋) (req : Json) {n : Nat} (Z Z2 : Zonotope (Vec 𝕋 n)) :
    Resp := do
  let ⟨r, M⟩ ← parseMatColsFixed dops.readExact Z2.h (← field req "M")
  let ρ ← dops.readExact "rho" (← scalarField req "rho")
  let H ← aux_rightInv dops req Z
  if h : r = Z.h then aux_optZ dops (Zonotope.minkDiffRep Z Z2 (fun i j => (h ▸ M) i j) ρ H)
  else throw s!"minkDiff: `M` has {r} rows, `Z` has {Z.h} generators"

/-- `minkDiff` with `method` `stretch`: `Zonotope.minkDiffStretch` at `mu`, or with `certify`
true `Zonotope.minkDiffStretchInner`. -/
private def aux_minkDiffStretch (dops : DtypeOps 𝕋) (req : Json) {n : Nat}
    (Z Z2 : Zonotope (Vec 𝕋 n)) : Resp := do
  let μ ← parseVecFixed dops.readExact Z.h (← field req "mu")
  let certify ← match fieldOpt req "certify" with
    | none => pure false
    | some j => match j.getBool? with
      | .ok b => pure b
      | .error _ => throw "minkDiff: `certify` must be a Boolean"
  if certify then
    aux_optZ dops (Zonotope.minkDiffStretchInner Z Z2 μ (← aux_rightInv dops req Z))
  else pure [aux_zField dops "Z" (Zonotope.minkDiffStretch Z Z2 μ)]

/-- `zonotope.minkDiff`: `Z ⊖ Z2` by `method` `rep`, `aligned` or `stretch`; `Z` or `null`. -/
def handleZonoMinkDiff (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "minkDiff" req ["Z", "Z2", "method", "M", "rho", "mu", "certify", "H"]
  let ⟨_, Z, Z2⟩ ← aux_pair dops req
  match ← strField req "method" with
  | "rep" => aux_minkDiffRep dops req Z Z2
  | "aligned" =>
    let ρ ← dops.readExact "rho" (← scalarField req "rho")
    if hh : Z.h = Z2.h then
      aux_optZ dops (Zonotope.minkDiffAligned Z Z2 hh ρ (← aux_rightInv dops req Z))
    else throw s!"minkDiff: `aligned` needs equal generator counts, {Z.h} and {Z2.h}"
  | "stretch" => aux_minkDiffStretch dops req Z Z2
  | m => throw s!"minkDiff: `method` must be rep, aligned or stretch, not `{m}`"

/-- `zonotope.reduceUnderApprox`: `Zonotope.reduceUnderApprox` with the proposal `Gr`; `Z` or
`null`. -/
def handleZonoReduceUnderApprox (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "reduceUnderApprox" req ["Z", "Gr", "H"]
  let dz ← parseZonotope dops.readExact (← field req "Z")
  -- the solver is the request's `Gr`, none where it is absent
  let opt : (Z : Zonotope (Vec 𝕋 dz.n)) → Option (Σ h : ℕ, Mat 𝕋 dz.n h) ←
    match fieldOpt req "Gr" with
    | none => pure fun _ => none
    | some gj =>
      let g ← parseMatRowsFixed dops.readExact dz.n gj
      pure fun _ => some g
  aux_optZ dops (Zonotope.reduceUnderApprox opt dz.Z (← aux_rightInv dops req dz.Z))

/-- `zonotope.underapproximate`: per direction `S_i` the `plus` and `minus` vertex, or `null`. -/
def handleZonoUnderapproximate (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "underapproximate" req ["Z", "S"]
  let dz ← parseZonotope dops.readExact (← field req "Z")
  let S ← (← arrField req "S").mapM (parseVecFixed dops.readExact dz.n)
  let tab := tableOf (Zonotope.rightInvCandidate fun i k => dz.Z.G k i)
  let H : Mat 𝕋 dz.Z.h dz.n := fun j i => tableGet FloatOps.zero tab j i
  let vert (s : Vec 𝕋 dz.n) (b : Bool) : Json :=
    match Zonotope.underapproximate dz.Z H s b with
    | some v => printVec dops.showExact v
    | none => Json.null
  let both (s : Vec 𝕋 dz.n) := Json.mkObj [("plus", vert s true), ("minus", vert s false)]
  pure [("V", Json.arr (S.map both))]

/-- `zonotope.dominantDirections`: `n` generators as columns, `null` when there are none. -/
def handleZonoDominantDirections (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "dominantDirections" req ["Z", "filterLength1", "filterLength2"]
  let dz ← parseZonotope dops.readExact (← field req "Z")
  let l1 ← match fieldOpt req "filterLength1" with
    | none => pure (dz.n + 5)
    | some _ => natField req "filterLength1"
  let l2 ← match fieldOpt req "filterLength2" with
    | none => pure (dz.n + 3)
    | some _ => natField req "filterLength2"
  match Zonotope.dominantDirections dz.Z l1 l2 with
  | some P => pure [("value", printMat dops.showExact P)]
  | none => pure [("value", Json.null)]

/-- `zonotope.filterOut`: the indices of the cells that no other cell is certified to contain. -/
def handleZonoFilterOut (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "filterOut" req ["Zs"]
  let zs ← arrField req "Zs"
  match zs[0]? with
  | none => pure [("value", Json.arr #[])]
  | some z0 =>
    let d0 ← parseZonotope dops.readExact z0
    let cells ← aux_cells dops req "Zs" d0.n
    let kept := Zonotope.filterOut (m := cells.size) (fun i => cells[i])
    pure [("value", Json.arr ((List.finRange cells.size).filter (· ∈ kept) |>.map
      fun i => Lean.toJson i.val).toArray)]

/-- `zonotope.encloseMany`: the oriented box around the cells along `direction`; `Z` is `null`
when the direction is the zero vector. -/
def handleZonoEncloseMany (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "encloseMany" req ["Zs", "direction", "p"]
  let dir ← parseVecDyn dops.readExact (← field req "direction")
  let p ← natField req "p"
  match dir with
  | ⟨0, _⟩ => throw "encloseMany: the dimension must be at least 1"
  | ⟨m + 1, d⟩ =>
    let cells ← aux_cells dops req "Zs" (m + 1)
    match hs : cells.size with
    | 0 => throw "encloseMany: `Zs` must not be empty"
    | q + 1 =>
      let zs : Fin (q + 1) → Zonotope (Vec 𝕋 (m + 1)) := fun i =>
        cells[i.val]'(by rw [hs]; exact i.2)
      match Zonotope.encloseMany p zs d with
      | some Z => pure [aux_zField dops "Z" Z]
      | none => pure [("Z", Json.null)]

/-- `zonotope.enclosePoints`: the Stursberg enclosure of the columns of `points` in basis `U`. -/
def handleZonoEnclosePoints (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "enclosePoints" req ["points", "U", "method"]
  match fieldOpt req "method" with
  | none => pure ()
  | some j =>
    unless j.getStr?.toOption = some "stursberg" do
      throw "enclosePoints: `method` must be `stursberg`, the only method modeled"
  let pts ← parseMatDyn dops.readExact (← field req "points")
  let ⟨r, U⟩ ← parseMatColsFixed dops.readExact pts.r (← field req "U")
  if h : r = pts.r then
    match hN : pts.c with
    | 0 => throw "enclosePoints: at least one point is required"
    | N + 1 =>
      haveI : NeZero (N + 1) := ⟨by omega⟩
      let P : Fin (N + 1) → Vec 𝕋 pts.r := fun j i => pts.M i (Fin.cast hN.symm j)
      pure [aux_zField dops "Z" (Zonotope.enclosePointsStursberg P (h ▸ U))]
  else throw s!"enclosePoints: `U` has {r} rows, the points have {pts.r}"

/-- `zonotope.vertices`: the corner list `V` (one column per vertex) and the error box `E`; the
walk `Zonotope.polygon` in the plane, `Zonotope.vPolytope` (`2 ^ h` corners) otherwise. -/
def handleZonoVertices (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "vertices" req ["Z"]
  let dz ← parseZonotope dops.readExact (← field req "Z")
  let out {n : Nat} (P : VPolytope (Vec 𝕋 n)) : Resp :=
    pure [("V", printMat dops.showExact (fun (i : Fin n) (l : Fin P.k) => P.V l i)),
      ("E", printIntervalVec dops.showExact P.I_error)]
  match dz with
  | ⟨2, Z⟩ => out (Zonotope.polygon Z)
  | ⟨_, Z⟩ =>
    if Z.h ≤ aux_maxGenerators then out (Zonotope.vPolytope Z)
    else throw s!"vertices: {Z.h} generators give 2^{Z.h} corners, the limit is \
      2^{aux_maxGenerators}"

/-- `zonotope.enlarge`: `ContSet.enlargeScalar`, the zonotope scaled about its center by `factor`,
a scalar or a column vector. -/
def handleZonoEnlarge (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "enlarge" req ["Z", "factor"]
  let dz ← parseZonotope dops.readExact (← field req "Z")
  let fj ← field req "factor"
  let f : Vec 𝕋 dz.n ←
    if (fieldOpt fj "rows").isSome then parseVecFixed dops.readExact dz.n fj
    else do
      let x ← dops.readExact "factor" (← scalarField req "factor")
      pure fun _ => x
  pure [aux_zField dops "Z" (ContSet.enlargeScalar (S := 𝒵[𝕋]) dz.Z f)]

/-- `zonotope.minus`: the point `v` subtracted, `ContSet.minusScalar`. -/
def handleZonoMinus (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "minus" req ["Z", "v"]
  let dz ← parseZonotope dops.readExact (← field req "Z")
  let v ← parseVecFixed dops.readExact dz.n (← field req "v")
  pure [aux_zField dops "Z" (ContSet.minusScalar (S := 𝒵[𝕋]) dz.Z v)]

/-- `zonotope.boundaryPoint`: the box `Zonotope.boundaryPoint` sweeps from `start` (default the
center) along `dir`, up to an upper bound of the exit step; `I` is `null` when no facet row bounds
the step. Not CORA's single LP point. -/
def handleZonoBoundaryPoint (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "boundaryPoint" req ["Z", "dir", "start"]
  let dz ← parseZonotope dops.readExact (← field req "Z")
  match dz with
  | ⟨0, _⟩ => throw "boundaryPoint: the zonotope must have dimension at least 1"
  | ⟨m + 1, Z⟩ =>
    let dir ← parseVecFixed dops.readExact (m + 1) (← field req "dir")
    let start ← match fieldOpt req "start" with
      | some j => parseVecFixed dops.readExact (m + 1) j
      | none => pure Z.c
    match Zonotope.boundaryPoint Z dir start with
    | some r => pure [("I", printIntervalVec dops.showExact r)]
    | none => pure [("I", Json.null)]

/-- `zonotope.projectOnHyperplane`: onto `{x | c · x = d}`, `c` a unit normal the caller has
normalised (CORA normalises first), `ContSet.projectOnHyperplaneFloat`. -/
def handleZonoProjectOnHyperplane (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "projectOnHyperplane" req ["Z", "c", "d"]
  let dz ← parseZonotope dops.readExact (← field req "Z")
  let c ← parseVecFixed dops.readExact dz.n (← field req "c")
  let d ← dops.readExact "d" (← scalarField req "d")
  pure [aux_zField dops "Z" (ContSet.projectOnHyperplaneFloat (S := 𝒵[𝕋]) dz.Z c d)]

/-- Every op of this file, without the `zonotope.` prefix. -/
def zonotopeOpNames : List String :=
  [ "abs", "and", "box", "cartProd", "center", "compact", "constrSat", "contains", "convHull",
    "cubMap", "dominantDirections", "enclose", "encloseMany", "enlarge", "boundaryPoint", "minus",
    "projectOnHyperplane", "enclosePoints", "exactPlus",
    "filterOut", "generatorLength", "intersectStrip", "isBounded", "isFullDim", "isIntersecting",
    "isequal", "lift", "minnorm", "norm", "origin", "project", "projectHighDim", "quadMap",
    "quadMapTri",
    "radius", "representsa", "rotate", "split", "splitFirstGen", "splitLongestGen",
    "supportFunc", "tensorMultiplication", "tensorMultiplication_zono", "underapproximate",
    "vertices", "zonotopeNorm", "or", "minkDiff", "reduceUnderApprox" ]

/-- `op` of `zonotope.`, run; `none` for a name this file does not serve. -/
@[noinline, nospecialize]
def handleZonotopeOp (dops : DtypeOps 𝕋) (op : String) (req : Json) : Option Resp :=
  match op with
  | "abs" => some (aux_unary op dops req [] fun Z => Zonotope.abs Z)
  | "and" => some (aux_binary op dops req fun Z S => Zonotope.and_ Z S)
  | "convHull" | "enclose" | "or" => some (aux_binary op dops req fun Z S => Zonotope.linComb Z S)
  -- the unary set ops and conversions
  | "box" => some (do
      checkFields op req ["Z"]
      let dz ← parseZonotope dops.readExact (← field req "Z")
      pure [("I", printIntervalVec dops.showExact (Zonotope.interval dz.Z))])
  | "cartProd" => some (handleZonoCartProd dops req)
  | "center" => some (do
      checkFields op req ["Z"]
      let dz ← parseZonotope dops.readExact (← field req "Z")
      pure [("value", printVec dops.showExact dz.Z.c)])
  | "compact" => some (do
      match fieldOpt req "method" with
      | none => pure ()
      | some j =>
        unless j.getStr?.toOption = some "zeros" do
          throw "compact: `method` must be `zeros`, the only method modeled"
      aux_unary op dops req ["method", "tol"] fun Z => Zonotope.compactZeros Z)
  -- the predicates
  | "constrSat" => some (handleZonoConstrSat dops req)
  | "contains" => some (handleZonoContains dops req)
  | "cubMap" => some (handleZonoCubMap dops req)
  -- the ops with certificate arguments filled by the library
  | "dominantDirections" => some (handleZonoDominantDirections dops req)
  | "encloseMany" => some (handleZonoEncloseMany dops req)
  | "enclosePoints" => some (handleZonoEnclosePoints dops req)
  | "enlarge" => some (handleZonoEnlarge dops req)
  | "boundaryPoint" => some (handleZonoBoundaryPoint dops req)
  | "minus" => some (handleZonoMinus dops req)
  | "projectOnHyperplane" => some (handleZonoProjectOnHyperplane dops req)
  | "exactPlus" => some (handleZonoExactPlus dops req)
  | "filterOut" => some (handleZonoFilterOut dops req)
  | "generatorLength" => some (handleZonoGeneratorLength dops req)
  | "intersectStrip" => some (handleZonoIntersectStrip dops req)
  | "isBounded" => some (aux_test op dops req [] fun _ => true)
  | "isFullDim" => some (handleZonoIsFullDim dops req)
  | "isIntersecting" => some (handleZonoIsIntersecting dops req)
  | "isequal" => some (do
      checkFields op req ["Z", "Z2", "tol"]
      checkTol op req
      let ⟨_, Z, Z2⟩ ← aux_pair dops req
      aux_bool (Zonotope.isequal Z Z2))
  -- coordinates and sizes
  | "lift" => some (handleZonoLift dops req)
  | "minnorm" => some (handleZonoMinnorm dops req)
  -- the norm, its options `type` and `mode` only at the defaults
  | "norm" => some (do
      checkFields op req ["Z", "type", "mode"]
      match fieldOpt req "type" with
      | none => pure ()
      | some j =>
        unless j.getNat?.toOption = some 2 || j.getStr?.toOption = some "2" do
          throw "norm: `type` must be 2, the float definition is the Euclidean norm"
      match fieldOpt req "mode" with
      | none => pure ()
      | some j =>
        unless j.getStr?.toOption = some "ub" do
          throw "norm: `mode` must be `ub`, the float definition is an upper bound"
      let dz ← parseZonotope dops.readExact (← field req "Z")
      pure [("normSq", Json.str (dops.showExact (Zonotope.normSq dz.Z)))])
  -- the origin and the maps of zonotopes
  | "origin" => some (do
      checkFields op req ["n"]
      pure [aux_zField dops "Z" (Zonotope.origin (𝕋 := 𝕋) (← natField req "n"))])
  | "project" => some (handleZonoProject dops req)
  | "projectHighDim" => some (handleZonoProjectHighDim dops req)
  | "quadMap" => some (handleZonoQuadMap dops req)
  | "quadMapTri" => some (handleZonoQuadMapTri dops req)
  -- the splits and the bounds
  | "radius" => some (handleZonoRadius dops req)
  | "representsa" => some (handleZonoRepresentsa dops req)
  | "rotate" => some (handleZonoRotate dops req)
  | "split" => some (handleZonoSplit dops req)
  | "splitFirstGen" | "splitLongestGen" => some (handleZonoSplitBy op dops req)
  | "supportFunc" => some (handleZonoSupportFunc dops req)
  | "tensorMultiplication" => some (handleZonoTensorMultiplication dops req)
  | "tensorMultiplication_zono" => some (handleZonoTensorMultiplicationZono dops req)
  | "underapproximate" => some (handleZonoUnderapproximate dops req)
  | "vertices" => some (handleZonoVertices dops req)
  | "zonotopeNorm" => some (handleZonoZonotopeNorm dops req)
  | "minkDiff" => some (handleZonoMinkDiff dops req)
  | "reduceUnderApprox" => some (handleZonoReduceUnderApprox dops req)
  | _ => none

end CORALean.Oracle


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
