import CORALean.ContSet.Capsule.Float.Operations.Basic
import CORALean.ContSet.ConZonotope.Float.Operations.Basic
import CORALean.ContSet.Ellipsoid.Float.Operations.Basic
import CORALean.ContSet.HPolytope.Float.Operations.Eqs
import CORALean.ContSet.Interval.Real.Definitions.NormType
import CORALean.ContSet.HPolytope.Float.Operations.Fullspace
import CORALean.ContSet.HPolytope.Real.Operations.RowLin
import CORALean.ContSet.VPolytope.Float.Operations.Basic
import CORALean.ContSet.ZonoBundle.Float.ZonoBundle
import CORALean.Examples.Oracle.Ops.OpCommon

/-!
# The wire format of the further set classes

Every class carries its error box as `E` (`{"inf","sup"}`, absent means zero). A halfspace
polytope is `{"A","b","Ae","be","b_error","be_error","E"}` (`Ae x = be`, absent means none), a
vertex polytope `{"V","E"}` (one column per vertex), a constrained zonotope `{"c","G","P","E"}`
with `P` a halfspace polytope on the coefficients, or CORA's `{"c","G","A","b","E"}` with `P` the
rows `A ξ = b` (the box `[-1,1]^h` is implicit), an ellipsoid `{"Q","q","E"}`, a capsule
`{"c","g","r","E"}`, a zonotope bundle `{"Zs":[zonotope, ...]}`, a matrix zonotope
`{"c","G":[matrix, ...],"E"}`, an interval matrix `{"inf","sup"}`.

## Inputs
* `n` – the dimension
* `j` – the JSON object

## Output
* the set, or an error naming the field
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Oracle

open CORALean CORALean.Float
open Lean (Json)

/-- A halfspace polytope whose dimension is a runtime value. -/
structure DynHPolytope (𝕋 : Type) where
  n : Nat
  P : HPolytope 𝕋 (Vec 𝕋 n)

/-- A vertex polytope whose dimension is a runtime value. -/
structure DynVPolytope (𝕋 : Type) where
  n : Nat
  P : VPolytope (Vec 𝕋 n)

/-- A constrained zonotope whose dimension is a runtime value. -/
structure DynConZonotope (𝕋 : Type) where
  n : Nat
  cZ : ConZonotope 𝕋 (Vec 𝕋 n)

/-- An ellipsoid whose dimension is a runtime value. -/
structure DynEllipsoid (𝕋 : Type) where
  n : Nat
  E : Ellipsoid 𝕋 n

/-- A capsule whose dimension is a runtime value. -/
structure DynCapsule (𝕋 : Type) where
  n : Nat
  C : Capsule 𝕋 n

/-- A zonotope bundle whose dimension is a runtime value. -/
structure DynZonoBundle (𝕋 : Type) where
  n : Nat
  zB : ZonoBundle (Vec 𝕋 n)

/-- A matrix zonotope whose shape is a runtime value. -/
structure DynMatZonotope (𝕋 : Type) where
  r : Nat
  c : Nat
  Z : Zonotope (Mat 𝕋 r c)

section codec

variable {𝕋 : Type} [FloatOps 𝕋] (readD : String → ExactScalar → Except String 𝕋)
  (showD : 𝕋 → String)


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The zero box of dimension `n`. -/
private def aux_zeroBox (n : Nat) : Interval (Vec 𝕋 n) :=
  ⟨fun _ => FloatOps.zero, fun _ => FloatOps.zero⟩

/-- `j`'s field `name` as a vector of length `n`, or zeros when the field is absent. -/
private def aux_vecOrZero (n : Nat) (j : Json) (name : String) : Except String (Vec 𝕋 n) :=
  match fieldOpt j name with
  | none => pure fun _ => FloatOps.zero
  | some v => parseVecFixed readD n v

/-- `j`'s field `E` as a box of dimension `n`, or the zero box when absent. -/
private def aux_boxOrZero (n : Nat) (j : Json) : Except String (Interval (Vec 𝕋 n)) :=
  match fieldOpt j "E" with
  | none => pure (aux_zeroBox n)
  | some v => parseIntervalVecFixed readD n v


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A halfspace polytope of the already-known dimension `n`. -/
def parseHPolytopeFixed (n : Nat) (j : Json) : Except String (HPolytope 𝕋 (Vec 𝕋 n)) := do
  let ⟨m, A⟩ ← parseMatColsFixed readD n (← field j "A")
  let b ← parseVecFixed readD m (← field j "b")
  let ⟨me, Ae⟩ ← match fieldOpt j "Ae" with
    | none => pure ⟨0, (fun _ _ => FloatOps.zero : Mat 𝕋 0 n)⟩
    | some v => parseMatColsFixed readD n v
  let be ← aux_vecOrZero readD me j "be"
  pure { m := m, A := fun i => A i, b := b, me := me, Ae := fun i => Ae i, be := be,
         b_error := ← aux_vecOrZero readD m j "b_error",
         be_error := ← aux_vecOrZero readD me j "be_error",
         I_error := ← aux_boxOrZero readD n j }

/-- A halfspace polytope, `n` read off the columns of `A`. -/
def parseHPolytope (j : Json) : Except String (DynHPolytope 𝕋) := do
  let n ← natField (← field j "A") "cols"
  pure ⟨n, ← parseHPolytopeFixed readD n j⟩

/-- A vertex polytope of the already-known dimension `n`. -/
def parseVPolytopeFixed (n : Nat) (j : Json) : Except String (VPolytope (Vec 𝕋 n)) := do
  let vj ← field j "V"
  let r ← natField vj "rows"
  if r ≠ n then throw s!"`V` has {r} rows, expected {n}"
  let dm ← parseMatDyn readD vj
  if h : dm.r = n then
    let M : Mat 𝕋 n dm.c := h ▸ dm.M
    pure { k := dm.c, V := fun l i => M i l, I_error := ← aux_boxOrZero readD n j }
  else throw s!"`V` has {dm.r} rows, expected {n}"

/-- A vertex polytope, `n` read off the rows of `V`. -/
def parseVPolytope (j : Json) : Except String (DynVPolytope 𝕋) := do
  let n ← natField (← field j "V") "rows"
  pure ⟨n, ← parseVPolytopeFixed readD n j⟩

/-- A constrained zonotope of the already-known dimension `n`. -/
def parseConZonotopeFixed (n : Nat) (j : Json) : Except String (ConZonotope 𝕋 (Vec 𝕋 n)) := do
  let c ← parseVecFixed readD n (← field j "c")
  let ⟨h, G⟩ ← parseMatRowsFixed readD n (← field j "G")
  let P ← match fieldOpt j "P" with
    | some pj => parseHPolytopeFixed readD h pj
    | none =>
      match fieldOpt j "A" with
      | none => pure (HPolytope.fullspace 𝕋 h)
      | some aj =>
        let ⟨q, Ae⟩ ← parseMatColsFixed readD h aj
        let be ← parseVecFixed readD q (← field j "b")
        pure (HPolytope.eqs Ae be)
  pure { h := h, c := c, G := fun l i => G i l, P := P, I_error := ← aux_boxOrZero readD n j }

/-- A constrained zonotope, `n` read off `c`. -/
def parseConZonotope (j : Json) : Except String (DynConZonotope 𝕋) := do
  let n ← natField (← field j "c") "rows"
  pure ⟨n, ← parseConZonotopeFixed readD n j⟩

/-- An ellipsoid of the already-known dimension `n`. -/
def parseEllipsoidFixed (n : Nat) (j : Json) : Except String (Ellipsoid 𝕋 n) := do
  let ⟨r, Q⟩ ← parseMatColsFixed readD n (← field j "Q")
  if h : r = n then
    pure { Q := h ▸ Q, q := ← parseVecFixed readD n (← field j "q"),
           I_error := ← aux_boxOrZero readD n j }
  else throw s!"`Q` must be {n}×{n}, not {r}×{n}"

/-- An ellipsoid, `n` read off `q`. -/
def parseEllipsoid (j : Json) : Except String (DynEllipsoid 𝕋) := do
  let n ← natField (← field j "q") "rows"
  pure ⟨n, ← parseEllipsoidFixed readD n j⟩

/-- A capsule of the already-known dimension `n`. -/
def parseCapsuleFixed (n : Nat) (j : Json) : Except String (Capsule 𝕋 n) := do
  let r ← match readD "r" (← scalarField j "r") with
    | .ok v => pure v
    | .error e => throw e
  pure { c := ← parseVecFixed readD n (← field j "c"), g := ← parseVecFixed readD n (← field j "g"),
         r := r, I_error := ← aux_boxOrZero readD n j }

/-- A capsule, `n` read off `c`. -/
def parseCapsule (j : Json) : Except String (DynCapsule 𝕋) := do
  let n ← natField (← field j "c") "rows"
  pure ⟨n, ← parseCapsuleFixed readD n j⟩

/-- A zonotope bundle of the already-known dimension `n`. -/
def parseZonoBundleFixed (n : Nat) (j : Json) : Except String (ZonoBundle (Vec 𝕋 n)) := do
  let zs ← (← arrField j "Zs").mapM (parseZonotopeFixed readD n)
  pure ⟨zs.size, fun i => zs[i]⟩

/-- A zonotope bundle, `n` read off its first zonotope. -/
def parseZonoBundle (j : Json) : Except String (DynZonoBundle 𝕋) := do
  let zs ← arrField j "Zs"
  match zs[0]? with
  | none => throw "a zonotope bundle needs at least one zonotope in `Zs`"
  | some z0 =>
    let n ← natField (← field z0 "c") "rows"
    pure ⟨n, ← parseZonoBundleFixed readD n j⟩

/-- A matrix zonotope, its shape read off `c`. -/
def parseMatZonotope (j : Json) : Except String (DynMatZonotope 𝕋) := do
  let dc ← parseMatDyn readD (← field j "c")
  let gs ← (← arrField j "G").mapM fun g => do
    let dg ← parseMatDyn readD g
    if h : dg.r = dc.r ∧ dg.c = dc.c then pure (h.1 ▸ h.2 ▸ dg.M : Mat 𝕋 dc.r dc.c)
    else throw s!"a generator is {dg.r}×{dg.c}, expected {dc.r}×{dc.c}"
  let E ← match fieldOpt j "E" with
    | none =>
      pure (⟨fun _ _ => FloatOps.zero, fun _ _ => FloatOps.zero⟩ : Interval (Mat 𝕋 dc.r dc.c))
    | some ej =>
      let db ← parseBoxMat readD ej
      if h : db.r = dc.r ∧ db.c = dc.c then pure (h.1 ▸ h.2 ▸ db.I : Interval (Mat 𝕋 dc.r dc.c))
      else throw s!"`E` is {db.r}×{db.c}, expected {dc.r}×{dc.c}"
  pure ⟨dc.r, dc.c, { h := gs.size, c := dc.M, G := fun i => gs[i], I_error := E }⟩

/-- `P` as the wire halfspace polytope. -/
def printHPolytope {n : Nat} (P : HPolytope 𝕋 (Vec 𝕋 n)) : Json :=
  Json.mkObj
    [ ("A", printMat showD (fun i j => P.A i j)), ("b", printVec showD P.b),
      ("Ae", printMat showD (fun i j => P.Ae i j)), ("be", printVec showD P.be),
      ("b_error", printVec showD P.b_error), ("be_error", printVec showD P.be_error),
      ("E", printIntervalVec showD P.I_error) ]

/-- `P` as the wire vertex polytope. -/
def printVPolytope {n : Nat} (P : VPolytope (Vec 𝕋 n)) : Json :=
  Json.mkObj
    [ ("V", printMat showD (fun i l : Fin _ => P.V l i)), ("E", printIntervalVec showD P.I_error) ]

/-- `cZ` as the wire constrained zonotope. -/
def printConZonotope {n : Nat} (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) : Json :=
  Json.mkObj
    [ ("c", printVec showD cZ.c), ("G", printMat showD (fun i l : Fin _ => cZ.G l i)),
      ("P", printHPolytope showD cZ.P), ("E", printIntervalVec showD cZ.I_error) ]

/-- `E` as the wire ellipsoid. -/
def printEllipsoid {n : Nat} (E : Ellipsoid 𝕋 n) : Json :=
  Json.mkObj
    [ ("Q", printMat showD E.Q), ("q", printVec showD E.q),
      ("E", printIntervalVec showD E.I_error) ]

/-- `C` as the wire capsule. -/
def printCapsule {n : Nat} (C : Capsule 𝕋 n) : Json :=
  Json.mkObj
    [ ("c", printVec showD C.c), ("g", printVec showD C.g), ("r", Json.str (showD C.r)),
      ("E", printIntervalVec showD C.I_error) ]

/-- `zB` as the wire zonotope bundle. -/
def printZonoBundle {n : Nat} (zB : ZonoBundle (Vec 𝕋 n)) : Json :=
  Json.mkObj [("Zs", Json.arr (Array.ofFn fun i : Fin zB.k => printZonotope showD (zB.Z i)))]

/-- `Z` as the wire matrix zonotope. -/
def printMatZonotope {r c : Nat} (Z : Zonotope (Mat 𝕋 r c)) : Json :=
  Json.mkObj
    [ ("c", printMat showD Z.c),
      ("G", Json.arr (Array.ofFn fun i : Fin Z.h => printMat showD (Z.G i))),
      ("E", printIntervalMat showD Z.I_error) ]

end codec

section helpers

variable {𝕋 : Type} [FloatOps 𝕋]

/-- The response `value` of a Boolean. -/
def valueBool (b : Bool) : Resp := pure [("value", Json.bool b)]

/-- The response `value` of a scalar. -/
def valueScalar (showD : 𝕋 → String) (x : 𝕋) : Resp := pure [("value", Json.str (showD x))]

/-- The permutation of `Fin N` a `lift` request's `dims` names, CORA's `lift_` being `project` at
`N` entries: `dims` must have `N` distinct entries, each below `N`. -/
def permFromDims (N : Nat) (dims : Array Nat) : Except String (Fin N ≃ Fin N) := do
  if hm : dims.size = N then
    if hlt : ∀ i : Fin dims.size, dims[i] < N then
      let f : Fin N → Fin N := fun i => ⟨dims[Fin.cast hm.symm i], hlt _⟩
      if hinj : Function.Injective f then
        have hsurj : ∀ j, ∃ i, f i = j := Finite.injective_iff_surjective.mp hinj
        pure
          { toFun := f
            invFun := fun j => Fin.find (fun i => f i = j) (hsurj j)
            left_inv := fun i => hinj (Fin.find_spec (p := fun i' => f i' = f i) (hsurj (f i)))
            right_inv := fun j => Fin.find_spec (p := fun i => f i = j) (hsurj j) }
      else throw "lift: `dims` must be a permutation, it repeats a coordinate"
    else throw s!"lift: every entry of `dims` must be below N = {N} (indices are 0-based)"
  else throw s!"lift: `dims` has {dims.size} entries but N = {N}, CORA's lift_ is not defined"

/-- `lift`'s `N` and `dims` for a set of dimension `n`: the permutation of `Fin n` to reindex by. -/
def liftPerm (req : Json) (n : Nat) : Except String (Fin n ≃ Fin n) := do
  let N ← natField req "N"
  let e ← permFromDims N (← natArrField req "dims")
  if h : N = n then pure (h ▸ e)
  else throw s!"lift: N = {N} differs from the dimension {n}, CORA's lift_ is not defined"

/-- A list of `n × n` matrices, the `Q` of `quadMap`. -/
def parseSquareList (readD : String → ExactScalar → Except String 𝕋) (n : Nat) (j : Json) :
    Except String (Σ m : Nat, Fin m → Mat 𝕋 n n) := do
  let qs ← (← j.getArr?).mapM fun mj => do
    let ⟨r, M⟩ ← parseMatColsFixed readD n mj
    if h : r = n then pure (h ▸ M) else throw s!"expected {n}×{n} matrices"
  pure ⟨qs.size, fun k => qs[k]⟩

/-- A third-order tensor `T`, `m` blocks of `n` matrices of `n × n`, the `T` of `cubMap`. -/
def parseTensor (readD : String → ExactScalar → Except String 𝕋) (n : Nat) (j : Json) :
    Except String (Σ m : Nat, Fin m → Fin n → Mat 𝕋 n n) := do
  let rows ← (← j.getArr?).mapM fun row => do
    (← row.getArr?).mapM fun mj => do
      let ⟨r, M⟩ ← parseMatColsFixed readD n mj
      if h : r = n then pure (h ▸ M) else throw s!"`T`: expected {n}×{n} matrices"
  if h : ∀ (i : Fin rows.size), (rows[i]).size = n then
    pure ⟨rows.size, fun i k => (rows[i]).getD k.val (fun _ _ => (FloatOps.zero : 𝕋))⟩
  else throw s!"`T`: every block must hold {n} matrices"

/-- The functional `x ↦ a · x`, which a support bound is asked about. -/
def rowFunctional [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : Nat} (a : Vec 𝕋 n) : Vec ℝ n →ₗ[ℝ] ℝ :=
  Real.HPolytope.rowLin (toRealMat (fun (_ : Fin 1) => a)) 0

/-- Accepts `req`'s `field` only at `want` (or absent), naming the modeled value otherwise. -/
def checkStrOption (op : String) (req : Json) (field : String) (want : String) :
    Except String Unit :=
  match fieldOpt req field with
  | none => pure ()
  | some j =>
    unless j.getStr?.toOption = some want do
      throw s!"{op}: `{field}` must be `{want}`, the only value CORALean's float {op} models"

/-- The set `{"n": n}` the two scalar-free classes are on the wire. -/
def printTrivialSet (n : Nat) : Json := Json.mkObj [("n", Lean.toJson n)]

/-- `lift`'s and `projectHighDim`'s `N` and `dims`, `dims` of length `n`. -/
def trivialDims (req : Json) (n : Nat) : Except String (Σ N : Nat, Fin n → Fin N) := do
  let N ← natField req "N"
  let ⟨m, d⟩ ← indexArrField req "dims" N
  if h : m = n then pure ⟨N, fun i => d (Fin.cast h.symm i)⟩
  else throw s!"`dims` has {m} entries, the dimension is {n}"

/-- Whether the other operand `S` is `{"empty":true}`, CORA's `isemptyobject(S)`. -/
def operandIsEmpty (req : Json) : Except String Bool := do
  let s ← field req "S"
  pure (match fieldOpt s "empty" with
    | some (Json.bool b) => b
    | _ => false)

/-- `type` of a norm: `1`, `inf` or `fro`. -/
def normTypeField (op : String) (req : Json) : Except String Real.Interval.NormType := do
  match fieldOpt req "type" with
  | none => throw s!"{op}: missing field `type` (1, inf or fro)"
  | some j =>
    if j.getNat?.toOption = some 1 || j.getStr?.toOption = some "1" then pure .one
    else match j.getStr?.toOption with
      | some "inf" => pure .inf
      | some "fro" => pure .fro
      | _ => throw s!"{op}: `type` must be 1, inf or fro"

end helpers

end CORALean.Oracle


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
