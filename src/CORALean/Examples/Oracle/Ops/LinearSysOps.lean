import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalCorrectionMatrixFloat
import CORALean.ContDynamics.LinearSys.Operations.CanonicalFormFloat
import CORALean.ContDynamics.LinearSys.Operations.ErrorSolutionAdaptiveFloat
import CORALean.ContDynamics.LinearSys.Operations.ExpIntervalFloat
import CORALean.ContDynamics.LinearSys.Operations.InputSolutionFloat
import CORALean.ContDynamics.LinearSys.Operations.IsCanonicalFormFloat
import CORALean.ContDynamics.LinearSys.Operations.OneStepFloat
import CORALean.ContDynamics.LinearSys.Operations.OneStepClosedFormFloat
import CORALean.ContDynamics.LinearSys.Operations.ReachFloat
import CORALean.ContDynamics.LinearSys.Operations.ReachFloatInput
import CORALean.ContDynamics.LinearSys.Operations.ReachStepkWrappingFreeFloat
import CORALean.ContDynamics.LinearSys.Operations.ReachWrappingFreeFloat
import CORALean.ContDynamics.LinearSys.Operations.ReachWrappingFreeFloatInput
import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalFloat
import CORALean.ContDynamics.LinearSys.Operations.TimePointStepFloat
import CORALean.ContDynamics.OutputEq.Operations.OutputSetNoise
import CORALean.ContSet.Zonotope.Float.Instances
import CORALean.Examples.Oracle.Ops.SetCodec
import CORALean.Specification.Instances

/-!
# The linear-system ops: CORA's `linearSys` methods

Thin adapters over the float definitions `references/coverage/contDynamics/linearSys.md` links.
A system is `{"A","B","c","C","D","k","E","F"}`, `A` square and the rest optional: `B`, `E`
default to no columns, `C` to the identity, `c`, `k` to zero (`ẋ = Ax + Bu + c + Ew`, `y = Cx +
Du + k + Fv`). Sets are zonotopes `{"c","G","E"}`, `timeStep`, `taylorTerms`, `zonotopeOrder`
CORA's names. `reach` takes `linAlg` `standard` or `wrapping-free`; with `U` or `c` it runs the
input variant. Not served: `reachBackward`, `reachInner`, `verify`, `initReach_adaptive`,
`trajectoryError`, `linearSysDT`, `nonlinearSys` (witness arguments, or a real-valued result).

## Inputs
* `dops` – dtype operations
* `req` – request

## Output
* the system, or an error message
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Oracle

open CORALean CORALean.Float
open Lean (Json)

/-- A linear system whose state dimension is a runtime value. -/
structure DynLinearSys (𝕋 : Type) where
  n : Nat
  sys : LinearSys 𝕋 n

section

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The identity matrix of the dtype. -/
private def aux_eye (d : Nat) : Mat 𝕋 d d :=
  fun i j => if i = j then FloatOps.one else FloatOps.zero

/-- `req`'s matrix `name` of `r` rows if present, its column count read off; none if absent. -/
private def aux_rows (dops : DtypeOps 𝕋) (req : Json) (name : String) (r : Nat) :
    Except String (Option (Σ c : Nat, Mat 𝕋 r c)) :=
  match fieldOpt req name with
  | none => pure none
  | some j => do pure (some (← parseMatRowsFixed dops.readExact r j))

/-- `req`'s vector `name` of length `d`, zero if absent. -/
private def aux_vec (dops : DtypeOps 𝕋) (req : Json) (name : String) (d : Nat) :
    Except String (Vec 𝕋 d) :=
  match fieldOpt req name with
  | none => pure fun _ => FloatOps.zero
  | some j => parseVecFixed dops.readExact d j

/-- A zero matrix. -/
private def aux_zeros (r c : Nat) : Mat 𝕋 r c := fun _ _ => FloatOps.zero

/-- Whether the exact-scalar matrix field `name` holds a nonzero entry. -/
private def aux_nonzero (req : Json) (name : String) : Except String Bool :=
  match fieldOpt req name with
  | none => pure false
  | some j => do
    let d ← parseMatScalarDyn j
    pure (!(d.data.all ExactScalar.isZero))

/-- `a / b` of two exact scalars as an exact fraction. -/
private def aux_ratOf : ExactScalar → ℚ
  | .dy ⟨m, e⟩ => if e ≥ 0 then (m * 2 ^ e.toNat : ℤ) else (m : ℚ) / (2 ^ (-e).toNat : ℕ)
  | .decNeg m d => (m : ℚ) / (10 ^ d : ℕ)

/-- The step count `(tFinal - tStart) / timeStep`, a nonnegative integer or an error naming it. -/
private def aux_steps (tStart tFinal timeStep : ℚ) : Except String Nat := do
  if timeStep ≤ 0 then throw "reach: `timeStep` must be positive"
  let q := (tFinal - tStart) / timeStep
  if q.den ≠ 1 ∨ q < 0 then
    throw s!"reach: (tFinal - tStart)/timeStep = {q} is not a nonnegative integer"
  pure q.num.toNat

/-- A zonotope list as the response array. -/
private def aux_zs (dops : DtypeOps 𝕋) {n : Nat} (l : List (Zonotope (Vec 𝕋 n))) : Json :=
  Json.arr (l.toArray.map (printZonotope dops.showExact))

/-- A set of the dimension `n` in field `name`. -/
private def aux_zono (dops : DtypeOps 𝕋) (req : Json) (name : String) (n : Nat) :
    Except String (Zonotope (Vec 𝕋 n)) := do
  parseZonotopeFixed dops.readExact n (← field req name)

/-- `Δt` read exactly into the dtype, the time grid unchanged. -/
private def aux_timeStep (dops : DtypeOps 𝕋) (req : Json) : Except String 𝕋 := do
  match dops.readExact "timeStep" (← scalarField req "timeStep") with
  | .ok v => pure v
  | .error _ => throw s!"timeStep is not exactly representable in {dops.label}, the time grid \
    would change"

/-- A scalar field read exactly into the dtype. -/
private def aux_scalar (dops : DtypeOps 𝕋) (req : Json) (name : String) : Except String 𝕋 := do
  dops.readExact name (← scalarField req name)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The system of the request: `A` square, `B`, `c`, `C`, `D`, `k`, `E`, `F` optional. -/
def parseLinearSys (dops : DtypeOps 𝕋) (req : Json) : Except String (DynLinearSys 𝕋) := do
  let dA ← parseMatDyn dops.readExact (← field req "A")
  if hA : dA.r = dA.c then
    let n := dA.r
    let A : Mat 𝕋 n n := cast (congrArg (Mat 𝕋 dA.r) hA.symm) dA.M
    let c ← aux_vec dops req "c" n
    let Bo ← aux_rows dops req "B" n
    let C ← match fieldOpt req "C" with
      | none => pure ⟨n, aux_eye n⟩
      | some j => parseMatColsFixed dops.readExact n j
    -- `D` has the rows of `C`
    let Do ← aux_rows dops req "D" C.1
    -- the input dimension: that of `B`, else of `D`, else none
    let m := match Bo, Do with
      | some B, _ => B.1
      | none, some D => D.1
      | none, none => 0
    let B : Mat 𝕋 n m := match Bo with
      | some B => if h : B.1 = m then cast (congrArg (Mat 𝕋 n) h) B.2 else aux_zeros n m
      | none => aux_zeros n m
    let D : Mat 𝕋 C.1 m := match Do with
      | some D => if h : D.1 = m then cast (congrArg (Mat 𝕋 C.1) h) D.2 else aux_zeros C.1 m
      | none => aux_zeros C.1 m
    if let some B' := Bo then
      if B'.1 ≠ m then throw "`B` and `D` disagree on the input dimension"
    if let some D' := Do then
      if D'.1 ≠ m then throw "`B` and `D` disagree on the input dimension"
    -- the output offset, the disturbance and the noise matrices, empty by default
    let k ← aux_vec dops req "k" C.1
    let Eo ← aux_rows dops req "E" n
    let Fo ← aux_rows dops req "F" C.1
    let E : Σ r : Nat, Mat 𝕋 n r := Eo.getD ⟨0, aux_zeros n 0⟩
    let F : Σ s : Nat, Mat 𝕋 C.1 s := Fo.getD ⟨0, aux_zeros C.1 0⟩
    pure ⟨n, ⟨m, C.1, E.1, F.1, A, B, c, C.2, D, k, E.2, F.2⟩⟩
  else throw s!"`A` must be square, not {dA.r}×{dA.c}"

/-- `sys` as the wire system. -/
def printLinearSys (showD : 𝕋 → String) {n : Nat} (sys : LinearSys 𝕋 n) : Json :=
  Json.mkObj
    [ ("A", printMat showD sys.A), ("B", printMat showD sys.B), ("c", printVec showD sys.c),
      ("C", printMat showD sys.C), ("D", printMat showD sys.D), ("k", printVec showD sys.k),
      ("E", printMat showD sys.E), ("F", printMat showD sys.F) ]

/-- `linearSys.reach`: the time-point and time-interval sets, `linAlg` `standard`
(`reachFloat`, `reachFloatInput`) or `wrapping-free` (`reachWrappingFreeFloat`, `...Input`). -/
def handleLinearSysReachOp (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "reach" req
    ["A", "B", "c", "C", "D", "k", "E", "F", "X0", "U", "tStart", "tFinal", "timeStep",
      "taylorTerms", "zonotopeOrder", "linAlg"]
  let d ← parseLinearSys dops req
  let sys := d.sys
  let X0 ← aux_zono dops req "X0" d.n
  let wrappingFree ← match fieldOpt req "linAlg" with
    | none => pure false
    | some j => match j.getStr?.toOption with
      | some "standard" => pure false
      | some "wrapping-free" => pure true
      | _ => throw "reach: `linAlg` must be `standard` or `wrapping-free`"
  -- the time horizon, exactly
  let tStart ← match fieldOpt req "tStart" with
    | none => pure (0 : ℚ)
    | some _ => pure (aux_ratOf (← scalarField req "tStart"))
  let tFinal := aux_ratOf (← scalarField req "tFinal")
  let Δt ← aux_timeStep dops req
  let _ ← aux_steps tStart tFinal (aux_ratOf (← scalarField req "timeStep"))
  let options : LinearSys.ReachFloatOptions 𝕋 :=
    { Δt := Δt, η := ← natField req "taylorTerms", ρ := ← natField req "zonotopeOrder" }
  -- an input set, or a nonzero offset `c`, is the input variant
  let hasInput := (fieldOpt req "U").isSome || (← aux_nonzero req "c")
  let fail : String := "reach: no admissible Taylor order was found for this timeStep"
  if hasInput then
    -- the input variant, the zero input set if only `c` drives it
    let U ← match fieldOpt req "U" with
      | some j => parseZonotopeFixed dops.readExact sys.m j
      | none => pure (Zonotope.origin (𝕋 := 𝕋) sys.m)
    let params : Reach.InputParams (Zonotope (Vec 𝕋 d.n)) (Zonotope (Vec 𝕋 sys.m)) ℚ :=
      { X₀ := X0, U := U, tStart := tStart, tFinal := tFinal }
    if wrappingFree then
      match LinearSys.reachWrappingFreeFloatInput sys params options with
      | none => throw fail
      | some Rti => pure [("timeInterval", aux_zs dops Rti)]
    else
      match LinearSys.reachFloatInput sys params options with
      | none => throw fail
      | some (Rti, Rtp) =>
        pure [("timePoint", aux_zs dops Rtp), ("timeInterval", aux_zs dops Rti)]
  else
    -- no input: the homogeneous run
    let params : Reach.Params (Zonotope (Vec 𝕋 d.n)) ℚ :=
      { X₀ := X0, tStart := tStart, tFinal := tFinal }
    if wrappingFree then
      match LinearSys.reachWrappingFreeFloat sys params options with
      | none => throw fail
      | some Rti => pure [("timeInterval", aux_zs dops Rti)]
    else
      match LinearSys.reachFloat sys params options with
      | none => throw fail
      | some (Rti, Rtp) =>
        pure [("timePoint", aux_zs dops Rtp), ("timeInterval", aux_zs dops Rti)]

/-- `linearSys.canonicalForm`: `[sys, U, u, V, v] = canonicalForm(sys, U, uVec, W, V, vVec)`. -/
def handleLinearSysCanonicalForm (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  -- the system, the input, disturbance and noise sets and their offsets
  checkFields "canonicalForm" req
    ["A", "B", "c", "C", "D", "k", "E", "F", "U", "uVec", "W", "V", "vVec"]
  let d ← parseLinearSys dops req
  let sys := d.sys
  let U ← aux_zono dops req "U" sys.m
  let uVec ← parseVecFixed dops.readExact sys.m (← field req "uVec")
  let W ← aux_zono dops req "W" sys.r
  let V ← aux_zono dops req "V" sys.s
  let vVec ← parseVecFixed dops.readExact sys.s (← field req "vVec")
  -- CORA's `canonicalForm`, line by line
  let (sys', U', u', V', v') := LinearSys.canonicalFormFloat sys U uVec W V vVec
  pure [("sys", printLinearSys dops.showExact sys'), ("U", printZonotope dops.showExact U'),
    ("u", printIntervalVec dops.showExact u'), ("V", printZonotope dops.showExact V'),
    ("v", printIntervalVec dops.showExact v')]

/-- `linearSys.outputSet`: `C R + D U + k`, plus `F V` if a noise set `V` is given. -/
def handleLinearSysOutputSet (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "outputSet" req ["A", "B", "c", "C", "D", "k", "E", "F", "R", "U", "V"]
  let d ← parseLinearSys dops req
  let sys := d.sys
  let R ← aux_zono dops req "R" d.n
  let U ← aux_zono dops req "U" sys.m
  match fieldOpt req "V" with
  | none => pure [("Z", printZonotope dops.showExact (sys.outputEq.outputSet (S := 𝒵[𝕋]) R U))]
  | some j =>
    let V ← parseZonotopeFixed dops.readExact sys.s j
    pure [("Z", printZonotope dops.showExact
      (sys.outputEq.outputSetNoise (S := 𝒵[𝕋]) sys.F R U V))]

/-- `linearSys.taylorMatrices`: `[e^{AΔt}]` and the correction matrix `[F]` at order `η`. -/
def handleLinearSysTaylorMatrices (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "taylorMatrices" req
    ["A", "B", "c", "C", "D", "k", "E", "F", "timeStep", "taylorTerms"]
  let d ← parseLinearSys dops req
  let Δt ← aux_timeStep dops req
  let η ← natField req "taylorTerms"
  pure [("eAdt", printIntervalMat dops.showExact (d.sys.expIntervalFloat Δt Δt η)),
    ("F", printIntervalMat dops.showExact
      (MatExp.intervalCorrectionMatrix (Interval.point d.sys.A) Δt η))]

/-- The one-set ops: a step's sets, solutions of the input and error terms. -/
def handleLinearSysStepOp (dops : DtypeOps 𝕋) (op : String) (req : Json) : Resp := do
  let sysFields := ["A", "B", "c", "C", "D", "k", "E", "F"]
  let d ← parseLinearSys dops req
  let sys := d.sys
  let n := d.n
  match op with
  -- one block of the reachable set: the time-point and time-interval sets
  | "oneStep" =>
    checkFields op req (sysFields ++ ["X", "U", "u", "timeStep", "taylorTerms"])
    let s := sys.oneStepFloat (← aux_zono dops req "X" n) (← aux_zono dops req "U" n)
      (← parseVecFixed dops.readExact n (← field req "u")) (← aux_timeStep dops req)
      (← natField req "taylorTerms")
    pure [("timePoint", printZonotope dops.showExact s.Rtp),
      ("timeInterval", printZonotope dops.showExact s.Rti)]
  -- CORA's closed form of the step: `none` when the exponential cannot be enclosed
  | "oneStepClosedForm" =>
    checkFields op req (sysFields ++ ["X", "U", "u", "timeStep", "taylorTerms"])
    match sys.oneStepClosedFormFloat (← aux_zono dops req "X" n) (← aux_zono dops req "U" n)
        (← parseVecFixed dops.readExact n (← field req "u")) (← aux_timeStep dops req)
        (← natField req "taylorTerms") with
    | none => pure [("timePoint", Json.null), ("timeInterval", Json.null)]
    | some s => pure [("timePoint", printZonotope dops.showExact s.Rtp),
        ("timeInterval", printZonotope dops.showExact s.Rti)]
  -- the homogeneous solution at the end of the step, and the whole step
  | "homogeneousSolution" =>
    checkFields op req (sysFields ++ ["X", "timeStep", "taylorTerms"])
    pure [("Z", printZonotope dops.showExact (sys.timePointStepFloat (← aux_timeStep dops req)
      (← natField req "taylorTerms") (← aux_zono dops req "X" n)))]
  | "post" =>
    checkFields op req (sysFields ++ ["X", "timeStep", "taylorTerms"])
    let Δt ← aux_timeStep dops req
    let η ← natField req "taylorTerms"
    let X ← aux_zono dops req "X" n
    pure [("timePoint", printZonotope dops.showExact (sys.timePointStepFloat Δt η X)),
      ("timeInterval", printZonotope dops.showExact (sys.timeIntervalFloat Δt η X))]
  -- the first window of the wrapping-free scheme, carried to step `k`
  | "initReach" =>
    checkFields op req (sysFields ++ ["Rtau", "timeStep", "taylorTerms", "step"])
    match sys.reachStepkWrappingFreeFloat (← aux_timeStep dops req) (← natField req "taylorTerms")
        (← aux_zono dops req "Rtau" n) (← natField req "step") with
    | none => pure [("Z", Json.null)]
    | some Z => pure [("Z", printZonotope dops.showExact Z)]
  -- the input solution, constant or time-varying
  | _ =>
    if op = "errorSolution_adaptive" then
      checkFields op req (sysFields ++ ["Vdyn", "Vstat", "timeStep", "taylorTerms"])
      let Vstat ← match fieldOpt req "Vstat" with
        | none => pure none
        | some j => do pure (some (← parseZonotopeFixed dops.readExact n j))
      pure [("Z", printZonotope dops.showExact (sys.errorSolutionAdaptiveFloat
        (← aux_timeStep dops req) (← natField req "taylorTerms") (← aux_zono dops req "Vdyn" n)
        Vstat))]
    else
      checkFields op req (sysFields ++ ["V", "r", "taylorTerms"])
      pure [("Z", printZonotope dops.showExact (sys.inputSolutionFloat
        (← aux_scalar dops req "r") (← natField req "taylorTerms") (← aux_zono dops req "V" n)))]

end

/-- Every op of this file, without the `linearSys.` prefix. -/
def linearSysOpNames : List String :=
  [ "reach", "canonicalForm", "isCanonicalForm", "outputSet", "taylorMatrices", "oneStep",
    "oneStepClosedForm",
    "homogeneousSolution", "post", "initReach", "errorSolution_adaptive", "affineSolution",
    "particularSolution_constant", "particularSolution_timeVarying" ]

/-- `op` of `linearSys.`, run; `none` for a name this file does not serve. -/
@[noinline, nospecialize]
def handleLinearSysOp {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]
    (dops : DtypeOps 𝕋) (op : String) (req : Json) : Option Resp :=
  match op with
  | "reach" => some (handleLinearSysReachOp dops req)
  | "canonicalForm" => some (handleLinearSysCanonicalForm dops req)
  | "isCanonicalForm" => some (do
      checkFields op req ["A", "B", "c", "C", "D", "k", "E", "F"]
      valueBool (LinearSys.isCanonicalFormFloat (← parseLinearSys dops req).sys))
  | "outputSet" => some (handleLinearSysOutputSet dops req)
  | "taylorMatrices" => some (handleLinearSysTaylorMatrices dops req)
  | "oneStep" | "oneStepClosedForm" | "homogeneousSolution" | "post" | "initReach"
  | "errorSolution_adaptive"
  | "affineSolution" | "particularSolution_constant" | "particularSolution_timeVarying" =>
    some (handleLinearSysStepOp dops op req)
  | _ => none

end CORALean.Oracle


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
