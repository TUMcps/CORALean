import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
import CORALean.ContSet.HPolytope.Real.Operations.RowLin
import CORALean.ContSet.Interval.Float.Operations.Acos
import CORALean.ContSet.Interval.Float.Operations.Acosh
import CORALean.ContSet.Interval.Float.Operations.Asin
import CORALean.ContSet.Interval.Float.Operations.Asinh
import CORALean.ContSet.Interval.Float.Operations.Atan
import CORALean.ContSet.Interval.Float.Operations.Atan2
import CORALean.ContSet.ContSet.Operations.ProjectOnHyperplaneFloat
import CORALean.ContSet.Interval.Float.Operations.Basic
import CORALean.ContSet.Interval.Float.Operations.BoundDot
import CORALean.ContSet.Interval.Float.Operations.BoundaryPoint
import CORALean.ContSet.Interval.Float.Operations.Center
import CORALean.ContSet.Interval.Float.Operations.Cos
import CORALean.ContSet.Interval.Float.Operations.Ctranspose
import CORALean.ContSet.Interval.Float.Operations.Dirac
import CORALean.ContSet.Interval.Float.Operations.Enlarge
import CORALean.ContSet.Interval.Float.Operations.Horzcat
import CORALean.ContSet.Interval.Float.Operations.IsFullDim
import CORALean.ContSet.Interval.Float.Instances
import CORALean.ContSet.Interval.Float.Operations.Isequal
import CORALean.ContSet.Interval.Float.Operations.Kron
import CORALean.ContSet.Interval.Float.Operations.Lift
import CORALean.ContSet.Interval.Float.Operations.Log
import CORALean.ContSet.Interval.Float.Operations.Lt
import CORALean.ContSet.Interval.Float.Operations.Mask
import CORALean.ContSet.Interval.Float.Operations.MatMul
import CORALean.ContSet.Interval.Float.Operations.MatPlus
import CORALean.ContSet.Interval.Float.Operations.MatPow
import CORALean.ContSet.Interval.Float.Operations.MinkDiff
import CORALean.ContSet.Interval.Float.Operations.Mrdivide
import CORALean.ContSet.Interval.Float.Operations.MtimesIntervalMat
import CORALean.ContSet.Interval.Float.Operations.Norm
import CORALean.ContSet.Interval.Float.Operations.Partition
import CORALean.ContSet.Interval.Float.Operations.Power
import CORALean.ContSet.Interval.Float.Operations.Prod1
import CORALean.ContSet.Interval.Float.Operations.ProjectHighDim
import CORALean.ContSet.Interval.Float.Operations.QuadMap
import CORALean.ContSet.Interval.Float.Operations.RadiusSq
import CORALean.ContSet.Interval.Float.Operations.Recip
import CORALean.ContSet.Interval.Float.Operations.Round
import CORALean.ContSet.Interval.Float.Operations.Sign
import CORALean.ContSet.Interval.Float.Operations.Sin
import CORALean.ContSet.Interval.Float.Operations.SplitAt
import CORALean.ContSet.Interval.Float.Operations.Sqrt
import CORALean.ContSet.Interval.Float.Operations.Sum1
import CORALean.ContSet.Interval.Float.Operations.Tan
import CORALean.ContSet.Interval.Float.Operations.Times
import CORALean.ContSet.Interval.Float.Operations.Transpose
import CORALean.ContSet.Interval.Float.Operations.Volume
import CORALean.Examples.Oracle.Ops.OpCommon
import CORALean.HybridDynamics.Parallel.Operations.IntervalStackProdFloat
import CORALean.Specification.Instances

/-!
# The interval ops: CORA's `interval` methods

Thin adapters over the float definitions `references/coverage/contSet/interval.md` links: parse,
call, print. Operands are `I`, `I2` (`{"inf","sup"}`); a set result is `I`, anything else `value`;
indices are 0-based; a field an op does not list is refused by name; `p`, `k` tune the
transcendental enclosures and are required. `true` of `contains`/`disjoint` is a proof.

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

/-- A response carrying the box `I` under `name`. -/
private def aux_boxField (dops : DtypeOps 𝕋) (name : String) {n : Nat}
    (I : Interval (Vec 𝕋 n)) : String × Json :=
  (name, printIntervalVec dops.showExact I)

/-- A response carrying the matrix box `I` under `name`. -/
private def aux_matBoxField (dops : DtypeOps 𝕋) (name : String) {r c : Nat}
    (I : Interval (Mat 𝕋 r c)) : String × Json :=
  (name, printIntervalMat dops.showExact I)

/-- A scalar of the dtype, `req`'s field `name`, read exactly. -/
private def aux_scalar (dops : DtypeOps 𝕋) (req : Json) (name : String) : Except String 𝕋 := do
  dops.readExact name (← scalarField req name)

/-- The box `I` of `req`, and the box `name` of the same dimension. -/
private def aux_pair (dops : DtypeOps 𝕋) (req : Json) (name : String) :
    Except String (Σ n : Nat, Interval (Vec 𝕋 n) × Interval (Vec 𝕋 n)) := do
  let b ← parseBox dops.readExact (← field req "I")
  let J ← parseIntervalVecFixed dops.readExact b.n (← field req name)
  pure ⟨b.n, b.I, J⟩

/-- Whether the interval operand `name` of `req` has one column, a vector rather than a matrix. -/
private def aux_isVec (req : Json) (name : String) : Bool :=
  match fieldOpt req name >>= (fieldOpt · "inf") >>= (fieldOpt · "cols") with
  | some c => c.getNat?.toOption = some 1
  | none => true

/-- A square `n × n` matrix, the field `j`. -/
private def aux_square (dops : DtypeOps 𝕋) (n : Nat) (j : Json) : Except String (Mat 𝕋 n n) := do
  let ⟨r, M⟩ ← parseMatColsFixed dops.readExact n j
  if h : r = n then pure (h ▸ M) else throw s!"expected an {n}×{n} matrix, got {r}×{n}"

/-- The bound of an `EBox`, `"-inf"`/`"inf"` where it is none. -/
private def aux_ebound (dops : DtypeOps 𝕋) (inf : String) : Option 𝕋 → Json
  | some x => Json.str (dops.showExact x)
  | none => Json.str inf

/-- An `EBox` as two column vectors, an unbounded side printed `"-inf"` / `"inf"`. -/
private def aux_ebox (dops : DtypeOps 𝕋) {n : Nat} (B : Interval.EBox 𝕋 n) : Json :=
  let col (g : Fin n → Json) : Json :=
    Json.mkObj [("rows", Lean.toJson n), ("cols", Lean.toJson (1 : Nat)),
      ("data", Json.arr (Array.ofFn g))]
  Json.mkObj [("inf", col fun i => aux_ebound dops "-inf" (B.lo i)),
    ("sup", col fun i => aux_ebound dops "inf" (B.hi i))]

/-- The scalar `x` as the response `value`. -/
private def aux_value (dops : DtypeOps 𝕋) (x : 𝕋) : Resp :=
  pure [("value", Json.str (dops.showExact x))]

/-- The Boolean `b` as the response `value`. -/
private def aux_bool (b : Bool) : Resp := pure [("value", Json.bool b)]

/-- A box in, a box out, `extra` the further fields `f`'s closure reads. -/
private def aux_unary (op : String) (dops : DtypeOps 𝕋) (req : Json) (extra : List String)
    (f : {n : Nat} → Interval (Vec 𝕋 n) → Interval (Vec 𝕋 n)) : Resp := do
  checkFields op req ("I" :: extra)
  let b ← parseBox dops.readExact (← field req "I")
  pure [aux_boxField dops "I" (f b.I)]

/-- A box in, a box out, tuned by `p`. -/
private def aux_unaryP (op : String) (dops : DtypeOps 𝕋) (req : Json)
    (f : {n : Nat} → Nat → Interval (Vec 𝕋 n) → Interval (Vec 𝕋 n)) : Resp := do
  let p ← natField req "p"
  aux_unary op dops req ["p"] fun I => f p I

/-- A box in, a box out, tuned by `p` and `k`. -/
private def aux_unaryPK (op : String) (dops : DtypeOps 𝕋) (req : Json)
    (f : {n : Nat} → Nat → Nat → Interval (Vec 𝕋 n) → Interval (Vec 𝕋 n)) : Resp := do
  let p ← natField req "p"
  let k ← natField req "k"
  aux_unary op dops req ["p", "k"] fun I => f p k I

/-- Two boxes of one dimension in, a box out. -/
private def aux_binary (op : String) (dops : DtypeOps 𝕋) (req : Json)
    (f : {n : Nat} → Interval (Vec 𝕋 n) → Interval (Vec 𝕋 n) → Interval (Vec 𝕋 n)) : Resp := do
  checkFields op req ["I", "I2"]
  let ⟨_, I, J⟩ ← aux_pair dops req "I2"
  pure [aux_boxField dops "I" (f I J)]

/-- Two boxes in, a Boolean out. -/
private def aux_test (op : String) (dops : DtypeOps 𝕋) (req : Json)
    (f : {n : Nat} → Interval (Vec 𝕋 n) → Interval (Vec 𝕋 n) → Bool) : Resp := do
  checkFields op req ["I", "I2", "tol"]
  checkTol op req
  let ⟨_, I, J⟩ ← aux_pair dops req "I2"
  aux_bool (f I J)

/-- A box in, a scalar out. -/
private def aux_scalarOut (op : String) (dops : DtypeOps 𝕋) (req : Json)
    (f : {n : Nat} → Interval (Vec 𝕋 n) → 𝕋) : Resp := do
  checkFields op req ["I"]
  let b ← parseBox dops.readExact (← field req "I")
  aux_value dops (f b.I)

/-- A box in, a vector out. -/
private def aux_vecOut (op : String) (dops : DtypeOps 𝕋) (req : Json)
    (f : {n : Nat} → Interval (Vec 𝕋 n) → Vec 𝕋 n) : Resp := do
  checkFields op req ["I"]
  let b ← parseBox dops.readExact (← field req "I")
  pure [("value", printVec dops.showExact (f b.I))]

/-- A matrix box in, a matrix box out. -/
private def aux_matUnary (op : String) (dops : DtypeOps 𝕋) (req : Json) (extra : List String)
    (f : {r c : Nat} → Interval (Mat 𝕋 r c) → Except String (String × Json)) : Resp := do
  checkFields op req ("I" :: extra)
  let b ← parseBoxMat dops.readExact (← field req "I")
  pure [← f b.I]

/-- `I` read as `n × 1` rows `dims`, the result's dimension `m` discovered. -/
private def aux_dims (req : Json) (n : Nat) : Except String (Σ m : Nat, Fin m → Fin n) :=
  indexArrField req "dims" n


/-- `p` of a one-parameter transcendental op, `(p, k)` of a two-parameter one. -/
private def aux_p (req : Json) : Except String Nat := natField req "p"

/-- `k` of a two-parameter transcendental op. -/
private def aux_k (req : Json) : Except String Nat := natField req "k"

/-- `norm`'s and `radius`'s CORA options, only the defaults being modeled. -/
private def aux_normOptions (op : String) (req : Json) : Except String Unit := do
  match fieldOpt req "type" with
  | none => pure ()
  | some j =>
    if j.getNat?.toOption = some 2 || j.getStr?.toOption = some "2" then pure ()
    else throw s!"{op}: `type` must be 2, the float definition is the Euclidean norm"
  match fieldOpt req "mode" with
  | none => pure ()
  | some j =>
    if j.getStr?.toOption = some "ub" then pure ()
    else throw s!"{op}: `mode` must be `ub`, the float definition is an upper bound"


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `interval.mtimes`: a real or interval matrix `M` times the box `I`, or an interval matrix
times an interval matrix. -/
def handleIntervalMtimes (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "mtimes" req ["M", "I"]
  let mj ← field req "M"
  let isBoxM := (fieldOpt mj "inf").isSome
  if aux_isVec req "I" then
    let b ← parseBox dops.readExact (← field req "I")
    if isBoxM then
      let ⟨_, IM⟩ ← parseIntervalMatColsFixed dops.readExact b.n mj
      pure [aux_boxField dops "I" (Interval.mtimesIntervalMat IM b.I)]
    else
      let ⟨_, M⟩ ← parseMatColsFixed dops.readExact b.n mj
      pure [aux_boxField dops "I" (Interval.mtimes M b.I)]
  else
    unless isBoxM do throw "mtimes: a real matrix times an interval matrix is not modeled"
    let bm ← parseBoxMat dops.readExact (← field req "I")
    let ⟨_, A⟩ ← parseIntervalMatColsFixed dops.readExact bm.r mj
    pure [aux_matBoxField dops "I" (Interval.matMul A bm.I)]

/-- `interval.plus`: `Interval.plus` at vectors, `Interval.matPlus` at matrices. -/
def handleIntervalPlus (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "plus" req ["I", "I2"]
  if aux_isVec req "I" then
    let ⟨_, I, J⟩ ← aux_pair dops req "I2"
    pure [aux_boxField dops "I" (Interval.plus I J)]
  else
    let a ← parseBoxMat dops.readExact (← field req "I")
    let b ← parseBoxMat dops.readExact (← field req "I2")
    if h : b.r = a.r ∧ b.c = a.c then
      pure [aux_matBoxField dops "I" (Interval.matPlus a.I (h.1 ▸ h.2 ▸ b.I))]
    else throw s!"plus: shapes {a.r}×{a.c} and {b.r}×{b.c} differ"

/-- `interval.contains` and `interval.isIntersecting` against a box `I2` or a zonotope `Z`. -/
def handleIntervalSetTest (op : String) (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields op req ["I", "I2", "Z", "tol"]
  checkTol op req
  let b ← parseBox dops.readExact (← field req "I")
  let key := if op = "contains" then "contains" else "disjoint"
  match fieldOpt req "Z", fieldOpt req "I2" with
  | some zj, none =>
    let Z ← parseZonotopeFixed dops.readExact b.n zj
    pure [(key, Json.bool (if op = "contains" then Contains.contains b.I Z
      else IsDisjoint.isDisjoint b.I Z))]
  | none, some ij =>
    let J ← parseIntervalVecFixed dops.readExact b.n ij
    letI : Contains (Interval (Vec 𝕋 b.n)) (Interval (Vec 𝕋 b.n)) :=
      containsBoxOuter (S := ℐ𝒱[𝕋])
    letI : IsDisjoint (Interval (Vec 𝕋 b.n)) (Interval (Vec 𝕋 b.n)) :=
      isDisjointBoxOuter (S := ℐ𝒱[𝕋])
    pure [(key, Json.bool (if op = "contains" then Contains.contains b.I J
      else IsDisjoint.isDisjoint b.I J))]
  | _, _ => throw s!"{op}: needs exactly one of `I2` (a box) and `Z` (a zonotope)"

/-- `interval.representsa`: `type` one of `emptySet`, `point`, `origin`. -/
def handleIntervalRepresentsa (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "representsa" req ["I", "type", "tol"]
  checkTol "representsa" req
  let b ← parseBox dops.readExact (← field req "I")
  match ← strField req "type" with
  -- `Interval.representsa_emptySet` (any `sup < inf`), with the dtype's own strict order
  | "emptySet" => aux_bool ((List.finRange b.n).any fun j => ltStrict (b.I.sup j) (b.I.inf j))
  | "point" => aux_bool (Interval.representsa_point b.I)
  | "origin" => aux_bool (Interval.representsa_origin b.I)
  | t => throw s!"representsa: `type` must be emptySet, point or origin, not `{t}`"

/-- `interval.supportFunc`: the upper bound of `dir · x` over the box, `Interval.boundDot`. -/
def handleIntervalSupportFunc (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "supportFunc" req ["I", "dir", "type"]
  let ty := (fieldOpt req "type").bind (·.getStr?.toOption)
  unless ty.isNone || ty = some "upper" do
    throw "supportFunc: `type` must be `upper`, the float definition bounds from above only"
  let b ← parseBox dops.readExact (← field req "I")
  let a ← parseVecFixed dops.readExact b.n (← field req "dir")
  let c : Vec ℝ b.n →ₗ[ℝ] ℝ := Real.HPolytope.rowLin (toRealMat (fun (_ : Fin 1) => a)) 0
  aux_value dops (Interval.boundDot b.I (c := c) a fun _ => rfl).val

/-- `interval.project`: the coordinates `dims`, 0-based. -/
def handleIntervalProject (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "project" req ["I", "dims"]
  let b ← parseBox dops.readExact (← field req "I")
  let ⟨_, d⟩ ← aux_dims req b.n
  pure [aux_boxField dops "I" (Interval.project b.I d)]

/-- `interval.projectHighDim` and `interval.lift`: `N` dimensions, coordinate `k` of `I` at
`dims[k]`. `lift` leaves the other coordinates unbounded. -/
def handleIntervalHighDim (op : String) (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields op req ["I", "N", "dims"]
  let b ← parseBox dops.readExact (← field req "I")
  let N ← natField req "N"
  let ⟨m, d⟩ ← indexArrField req "dims" N
  if h : m = b.n then
    let I : Interval (Vec 𝕋 m) := h ▸ b.I
    if op = "lift" then pure [("I", aux_ebox dops (Interval.lift_ I N d))]
    else pure [aux_boxField dops "I" (Interval.projectHighDim_ I N d)]
  else throw s!"{op}: `dims` has {m} entries, the dimension of `I` is {b.n}"

/-- `interval.split`: bisection of coordinate `dim`, 0-based. -/
def handleIntervalSplit (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "split" req ["I", "dim"]
  let b ← parseBox dops.readExact (← field req "I")
  let j ← indexField req "dim" b.n
  let (I1, I2) := Interval.splitAt b.I j
  pure [aux_boxField dops "I1" I1, aux_boxField dops "I2" I2]

/-- `interval.partition`: the cell `ind` of the grid of `splits` cells per coordinate. -/
def handleIntervalPartition (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "partition" req ["I", "splits", "ind"]
  let b ← parseBox dops.readExact (← field req "I")
  let splits ← natField req "splits"
  let ⟨m, d⟩ ← indexArrField req "ind" splits
  if h : m = b.n then
    pure [aux_boxField dops "I" (Interval.partition b.I splits (h ▸ d))]
  else throw s!"partition: `ind` has {m} entries, the dimension of `I` is {b.n}"

/-- `interval.boundaryPoint`: where the ray from `start` along `dir` leaves the box; `I` is
`null` when it does not. -/
def handleIntervalBoundaryPoint (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "boundaryPoint" req ["I", "dir", "start"]
  let b ← parseBox dops.readExact (← field req "I")
  let dir ← parseVecFixed dops.readExact b.n (← field req "dir")
  let start ← parseVecFixed dops.readExact b.n (← field req "start")
  match Interval.boundaryPoint b.I dir start with
  | some r => pure [aux_boxField dops "I" r]
  | none => pure [("I", Json.null)]

/-- `interval.projectOnHyperplane`: onto `{x | c · x = d}`, `c` a unit normal the caller has
normalised (CORA normalises first), `ContSet.projectOnHyperplaneFloat`. -/
def handleIntervalProjectOnHyperplane (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "projectOnHyperplane" req ["I", "c", "d"]
  let b ← parseBox dops.readExact (← field req "I")
  let c ← parseVecFixed dops.readExact b.n (← field req "c")
  let d ← dops.readExact "d" (← scalarField req "d")
  pure [aux_boxField dops "I" (ContSet.projectOnHyperplaneFloat (S := ℐ𝒱[𝕋]) b.I c d)]

/-- `interval.cartProd`: the box of the two boxes stacked, `Interval.stackProd`. -/
def handleIntervalCartProd (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "cartProd" req ["I", "I2"]
  let a ← parseBox dops.readExact (← field req "I")
  let b ← parseBox dops.readExact (← field req "I2")
  let bs : (i : Fin 2) → Interval (Vec 𝕋 (![a.n, b.n] i)) := fun i =>
    match i with
    | 0 => a.I
    | 1 => b.I
  pure [aux_boxField dops "I" (Interval.stackProd bs)]

/-- `interval.enclosePoints`: the box around the columns of `points`. -/
def handleIntervalEnclosePoints (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "enclosePoints" req ["points"]
  let dm ← parseMatDyn dops.readExact (← field req "points")
  pure [aux_boxField dops "I"
    (Interval.enclosePoints (n := dm.r) fun (j : Fin dm.c) (i : Fin dm.r) => dm.M i j)]

/-- `interval.quadMap`: `Q` an array of `n × n` matrices. -/
def handleIntervalQuadMap (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "quadMap" req ["I", "Q"]
  let b ← parseBox dops.readExact (← field req "I")
  let qs ← (← arrField req "Q").mapM (aux_square dops b.n)
  pure [aux_boxField dops "I" (Interval.quadMap (m := qs.size) (fun k => qs[k]) b.I)]

/-- `interval.sum`: `dim` 1 sums the rows, `dim` 2 the columns. -/
def handleIntervalSum (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  let dim ← natField req "dim"
  aux_matUnary "sum" dops req ["dim"] fun I =>
    match dim with
    | 1 => pure (aux_boxField dops "I" (Interval.sum₁ I))
    | 2 => pure (aux_boxField dops "I" (Interval.sum₂ I))
    | d => throw s!"sum: `dim` must be 1 or 2, not {d}"

/-- `interval.diag`: a vector to a diagonal matrix, a square matrix to its diagonal. -/
def handleIntervalDiag (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "diag" req ["I"]
  if aux_isVec req "I" then
    let b ← parseBox dops.readExact (← field req "I")
    pure [aux_matBoxField dops "I" (Interval.diag b.I)]
  else
    let b ← parseBoxMat dops.readExact (← field req "I")
    if h : b.c = b.r then pure [aux_boxField dops "I" (Interval.diagVec (h ▸ b.I))]
    else throw s!"diag: a matrix must be square, not {b.r}×{b.c}"

/-- `interval.mpower`: the interval matrix `I` to the natural power `exponent`. -/
def handleIntervalMpower (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  let k ← natField req "exponent"
  aux_matUnary "mpower" dops req ["exponent"] fun {r c} I =>
    if h : c = r then pure (aux_matBoxField dops "I" (Interval.matPow (h ▸ I) k))
    else throw s!"mpower: a matrix must be square, not {r}×{c}"

/-- `interval.tril` and `interval.triu`: the entries on or below (above) the `K`-th diagonal. -/
def handleIntervalTri (op : String) (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  let K ← match fieldOpt req "K" with
    | none => pure 0
    | some _ => natField req "K"
  aux_matUnary op dops req ["K"] fun I =>
    pure (aux_matBoxField dops "I" (if op = "tril" then Interval.tril K I else Interval.triu K I))

/-- `interval.kron`, `horzcat`, `vertcat` of two interval matrices, named `name` in messages and
choosing the operation by `op`. -/
def handleIntervalMatBinary (name op : String) (extra : List String) (dops : DtypeOps 𝕋)
    (req : Json) : Resp := do
  checkFields name req (["I", "I2"] ++ extra)
  let a ← parseBoxMat dops.readExact (← field req "I")
  let b ← parseBoxMat dops.readExact (← field req "I2")
  match op with
  | "kron" => pure [aux_matBoxField dops "I" (Interval.kron a.I b.I)]
  | "horzcat" =>
    if h : b.r = a.r then pure [aux_matBoxField dops "I" (Interval.horzcat a.I (h ▸ b.I))]
    else throw s!"{name}: {a.r} and {b.r} rows"
  | _ =>
    if h : b.c = a.c then pure [aux_matBoxField dops "I" (Interval.vertcat a.I (h ▸ b.I))]
    else throw s!"{name}: {a.c} and {b.c} columns"

/-- `interval.cat`: `dim` 1 stacks the matrices vertically, `dim` 2 horizontally. -/
def handleIntervalCat (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  match ← natField req "dim" with
  | 1 => handleIntervalMatBinary "cat" "vertcat" ["dim"] dops req
  | 2 => handleIntervalMatBinary "cat" "horzcat" ["dim"] dops req
  | d => throw s!"cat: `dim` must be 1 or 2, not {d}"

/-- `interval.empty`, `interval.origin`: the `n`-dimensional box. -/
def handleIntervalConst (op : String) (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields op req ["n"]
  let n ← natField req "n"
  match op with
  | "empty" => pure [aux_boxField dops "I" (Interval.empty (𝕋 := 𝕋) n)]
  | _ => pure [aux_boxField dops "I" (Interval.origin (𝕋 := 𝕋) n)]

/-- `interval.Inf`: the whole space, `n` unbounded coordinates. -/
def handleIntervalInf (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "Inf" req ["n"]
  let n ← natField req "n"
  pure [("I", aux_ebox dops (Interval.Inf (𝕋 := 𝕋) n))]

/-- `interval.dirac`: the box of a Dirac-delta weight, `n` the CORA argument. -/
def handleIntervalDirac (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "dirac" req ["I", "n"]
  let b ← parseBox dops.readExact (← field req "I")
  let n ← natField req "n"
  pure [("I", aux_ebox dops (Interval.dirac n b.I))]

/-- `interval.intervalMatrix`: the interval matrix with center `c` and radius `r`. -/
def handleIntervalMatrix (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "intervalMatrix" req ["c", "r"]
  let c ← parseMatDyn dops.readExact (← field req "c")
  let r ← parseMatDyn dops.readExact (← field req "r")
  if h : r.r = c.r ∧ r.c = c.c then
    pure [aux_matBoxField dops "I" (Interval.ofCenterRadius c.M (h.1 ▸ h.2 ▸ r.M))]
  else throw s!"intervalMatrix: `c` is {c.r}×{c.c} but `r` is {r.r}×{r.c}"

/-- `interval.zonotope`: the zonotope of the box. -/
def handleIntervalZonotope (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "zonotope" req ["I"]
  let b ← parseBox dops.readExact (← field req "I")
  pure [("Z", printZonotope dops.showExact (Interval.zonotope b.I))]

/-- `interval.vertices`: the corners `V` of the box, one per column, and the error box `E`. -/
def handleIntervalVertices (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "vertices" req ["I"]
  let b ← parseBox dops.readExact (← field req "I")
  let P := Interval.vPolytope b.I
  pure [("V", printMat dops.showExact (fun (i : Fin b.n) (l : Fin P.k) => P.V l i)),
    ("E", printIntervalVec dops.showExact P.I_error)]

/-- `interval.reduce`: a box is its own order, so this is `Reduce.reduce`, the storage-only
`materialise`; `method` is accepted because every method gives the same box. -/
def handleIntervalReduce (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "reduce" req ["I", "order", "method"]
  let _ ← natField req "order"
  let b ← parseBox dops.readExact (← field req "I")
  pure [aux_boxField dops "I" (Reduce.reduce b.I (← natField req "order"))]

/-- Every op of this file, without the `interval.` prefix. -/
def intervalOpNames : List String :=
  [ "abs", "uminus", "uplus", "sign", "round", "sqrt", "exp", "log", "sin", "cos", "tan", "sinh",
    "cosh", "tanh", "asin", "acos", "atan", "asinh", "acosh", "atanh", "atan2", "enlarge", "power",
    "rdivide", "mrdivide", "plus", "minus", "times", "and", "or", "convHull", "minkDiff", "min",
    "max", "enclose", "le", "lt", "isequal", "isFullDim", "isBounded", "representsa", "contains",
    "isIntersecting", "center", "rad", "radius", "norm", "volume", "supportFunc", "infimum",
    "supremum", "project", "lift", "projectHighDim", "split", "partition", "boundaryPoint",
    "cartProd", "projectOnHyperplane", "enclosePoints", "quadMap", "mtimes", "transpose",
    "ctranspose", "sum", "prod",
    "diag", "mpower", "tril", "triu", "kron", "horzcat", "vertcat", "cat", "empty", "origin", "Inf",
    "dirac", "intervalMatrix", "zonotope", "vertices", "reduce" ]

/-- `op` of `interval.`, run; `none` for a name this file does not serve. -/
@[noinline, nospecialize]
def handleIntervalOp (dops : DtypeOps 𝕋) (op : String) (req : Json) : Option Resp :=
  match op with
  | "abs" => some (aux_unary op dops req [] fun I => Interval.abs I)
  | "uminus" => some (aux_unary op dops req [] fun I => Interval.uminus I)
  | "uplus" => some (aux_unary op dops req [] fun I => Interval.uplus I)
  | "sign" => some (aux_unary op dops req [] fun I => Interval.sign I)
  | "round" => some (aux_unary op dops req [] fun I => Interval.round I)
  -- the elementary functions, `p` (and `k`) the enclosure tuning
  | "sqrt" => some (aux_unaryP op dops req fun p I => Interval.sqrt p I)
  | "exp" => some (aux_unaryP op dops req fun p I => Interval.exp p I)
  | "sin" => some (aux_unaryP op dops req fun p I => Interval.sin p I)
  | "cos" => some (aux_unaryP op dops req fun p I => Interval.cos p I)
  | "tan" => some (do
      let p ← natField req "p"
      checkFields op req ["I", "p"]
      let b ← parseBox dops.readExact (← field req "I")
      pure [("I", aux_ebox dops (Interval.tan p b.I))])
  | "sinh" => some (aux_unaryP op dops req fun p I => Interval.sinh p I)
  | "cosh" => some (aux_unaryP op dops req fun p I => Interval.cosh p I)
  | "tanh" => some (aux_unaryP op dops req fun p I => Interval.tanh p I)
  -- the same with two tuning parameters
  | "log" => some (aux_unaryPK op dops req fun p k I => Interval.log p k I)
  | "asin" => some (aux_unaryPK op dops req fun p k I => Interval.asin p k I)
  | "acos" => some (aux_unaryPK op dops req fun p k I => Interval.acos p k I)
  | "atan" => some (aux_unaryPK op dops req fun p k I => Interval.atan p k I)
  | "asinh" => some (aux_unaryPK op dops req fun p k I => Interval.asinh p k I)
  | "acosh" => some (aux_unaryPK op dops req fun p k I => Interval.acosh p k I)
  | "atanh" => some (aux_unaryPK op dops req fun p k I => Interval.atanh p k I)
  -- the two-operand and parametrised arithmetic
  | "atan2" => some (do
      let p ← aux_p req; let k ← aux_k req
      checkFields op req ["I", "I2", "p", "k"]
      let ⟨_, I, J⟩ ← aux_pair dops req "I2"
      pure [aux_boxField dops "I" (Interval.atan2 p k I J)])
  -- the arithmetic, scalar arguments read first
  | "enlarge" => some (do
      let f ← aux_scalar dops req "factor"
      aux_unary op dops req ["factor"] fun I => Interval.enlarge I f)
  | "power" => some (do
      let k ← natField req "exponent"
      aux_unary op dops req ["exponent"] fun I => Interval.power I k)
  | "mrdivide" => some (do
      let d ← aux_scalar dops req "d"
      aux_unary op dops req ["d"] fun I => Interval.mrdivide I d)
  | "rdivide" => some (aux_binary op dops req fun I J => Interval.rdivide I J)
  | "plus" => some (handleIntervalPlus dops req)
  | "minus" => some (aux_binary op dops req fun I J => Interval.minus I J)
  | "times" => some (aux_binary op dops req fun I J => Interval.times I J)
  | "and" => some (aux_binary op dops req fun I J => Interval.intersection I J)
  | "or" => some (aux_binary op dops req fun I J => Interval.or I J)
  | "convHull" => some (aux_binary op dops req fun I J => Interval.convHull I J)
  | "minkDiff" => some (aux_binary op dops req fun I J => Interval.minkDiff I J)
  | "min" => some (aux_binary op dops req fun I J => Interval.min I J)
  | "max" => some (aux_binary op dops req fun I J => Interval.max I J)
  | "enclose" => some (aux_binary op dops req fun I J => Interval.linComb I J)
  -- the tests, certified in one direction only
  | "le" => some (aux_test op dops req fun I J => Interval.le I J)
  | "lt" => some (aux_test op dops req fun I J => Interval.lt I J)
  | "isequal" => some (aux_test op dops req fun I J => Interval.isequal I J)
  | "isFullDim" => some (do
      checkFields op req ["I", "tol"]
      checkTol op req
      let b ← parseBox dops.readExact (← field req "I")
      aux_bool (Interval.isFullDim b.I))
  | "isBounded" => some (do
      checkFields op req ["I", "tol"]
      checkTol op req
      let _ ← parseBox dops.readExact (← field req "I")
      aux_bool true)
  | "representsa" => some (handleIntervalRepresentsa dops req)
  | "contains" | "isIntersecting" => some (handleIntervalSetTest op dops req)
  -- scalars and vectors read off the box
  | "center" => some (aux_vecOut op dops req fun I => Interval.center I)
  | "rad" => some (aux_vecOut op dops req fun I => Interval.radius I)
  | "infimum" => some (aux_vecOut op dops req fun I => Interval.infimum I)
  | "supremum" => some (aux_vecOut op dops req fun I => Interval.supremum I)
  | "radius" => some (do
      aux_normOptions op req
      checkFields op req ["I", "type", "mode"]
      let b ← parseBox dops.readExact (← field req "I")
      pure [("radiusSq", Json.str (dops.showExact (Interval.radiusSq b.I)))])
  | "norm" => some (do
      aux_normOptions op req
      checkFields op req ["I", "type", "mode"]
      let b ← parseBox dops.readExact (← field req "I")
      pure [("normSq", Json.str (dops.showExact (Interval.normSq b.I)))])
  | "volume" => some (aux_scalarOut op dops req fun I => Interval.volume I)
  | "supportFunc" => some (handleIntervalSupportFunc dops req)
  -- changing the dimension
  | "project" => some (handleIntervalProject dops req)
  | "lift" | "projectHighDim" => some (handleIntervalHighDim op dops req)
  | "split" => some (handleIntervalSplit dops req)
  | "partition" => some (handleIntervalPartition dops req)
  | "boundaryPoint" => some (handleIntervalBoundaryPoint dops req)
  | "cartProd" => some (handleIntervalCartProd dops req)
  | "projectOnHyperplane" => some (handleIntervalProjectOnHyperplane dops req)
  | "enclosePoints" => some (handleIntervalEnclosePoints dops req)
  | "quadMap" => some (handleIntervalQuadMap dops req)
  -- interval matrices
  | "mtimes" => some (handleIntervalMtimes dops req)
  | "transpose" => some (aux_matUnary op dops req [] fun I =>
      pure (aux_matBoxField dops "I" (Interval.transpose I)))
  | "ctranspose" => some (aux_matUnary op dops req [] fun I =>
      pure (aux_matBoxField dops "I" (Interval.ctranspose I)))
  | "sum" => some (handleIntervalSum dops req)
  -- CORA's `prod` of a matrix is the row of the column products, `1 × n`
  | "prod" => some (aux_matUnary op dops req [] fun I =>
      let P := Interval.prod₁ I
      pure (aux_matBoxField dops "I"
        (⟨fun _ j => P.inf j, fun _ j => P.sup j⟩ : Interval (Mat 𝕋 1 _))))
  | "diag" => some (handleIntervalDiag dops req)
  | "mpower" => some (handleIntervalMpower dops req)
  | "tril" | "triu" => some (handleIntervalTri op dops req)
  | "kron" => some (handleIntervalMatBinary op op [] dops req)
  | "horzcat" | "vertcat" => some (handleIntervalMatBinary op op [] dops req)
  | "cat" => some (handleIntervalCat dops req)
  -- constructors and conversions
  | "empty" | "origin" => some (handleIntervalConst op dops req)
  | "Inf" => some (handleIntervalInf dops req)
  | "dirac" => some (handleIntervalDirac dops req)
  | "intervalMatrix" => some (handleIntervalMatrix dops req)
  | "zonotope" => some (handleIntervalZonotope dops req)
  | "vertices" => some (handleIntervalVertices dops req)
  | "reduce" => some (handleIntervalReduce dops req)
  | _ => none

end CORALean.Oracle


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
