import CORALean.ContDynamics.NonlinearSys.Operations.LinReachFloat
import CORALean.ContDynamics.NonlinearSys.Operations.ReachAlgFloat
import CORALean.ContDynamics.NonlinearSys.Operations.LinReachAdaptiveInit
import CORALean.ContDynamics.NonlinearSys.Operations.ReachAdaptiveFloat
import CORALean.ContDynamics.NonlinearSys.Operations.AdaptiveOrdersFloat
import CORALean.ContDynamics.NonlinearSys.Operations.LinReachPolyAdaptiveInit
import CORALean.ContDynamics.NonlinearSys.Operations.ReachPolyAdaptiveFloat
import CORALean.Examples.Oracle.Ops.PolyZonotopeCodec
import CORALean.ContSet.Interval.Float.Operations.Basic
import CORALean.ContSet.Interval.Float.Operations.Cos
import CORALean.ContSet.Interval.Float.Operations.Power
import CORALean.ContSet.Interval.Float.Operations.Sin
import CORALean.ContSet.Interval.Float.Operations.Sqrt
import CORALean.ContSet.Interval.Float.Operations.Times
import CORALean.Examples.Oracle.Ops.SetCodec
import CORALean.ContSet.Interval.Float.Operations.Tan
import CORALean.ContSet.Interval.Float.Operations.Atan
import CORALean.ContSet.Interval.Float.Operations.Log
import CORALean.Global.Float.NoNaN
import CORALean.Specification.Instances

/-!
# The nonlinear-system ops: CORA's `linReach` on a dynamics tree

The dynamics are an expression tree of the request, evaluated over boxes by the interval natural
extension and differentiated symbolically, which gives the `FloatHessModel` that `linReachFloat`
takes. Its enclosure property (`FloatHessModel.Encloses`, the hypothesis of `linReachFloat_outer`)
is by construction, not proved in Lean, so the ops are served at `nearest` only and refused at
every guaranteed dtype. An operand outside an elementary function's domain (a division by a box
holding 0, `sqrt` of a negative box) is not refused but evaluated by CORALean's definition. The tree
and the ops, the `…Adaptive` ones (CORA's `lin-adaptive`, repaired) too, are in
`experiments/oracle/README.md`. `tan` is served where its enclosure is bounded on every box.

## Inputs
* `dops` – dtype operations
* `req` – request

## Output
* response fields or an error message
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Oracle

open CORALean CORALean.Float
open Lean (Json)

/-- A dynamics tree over the scalar `𝕋`: variables `x_i`, inputs `u_j`, constants and the
operations of the wire format. -/
inductive DynExpr (𝕋 : Type) where
  | zero | one
  | const (c : 𝕋)
  | x (i : Nat)
  | u (j : Nat)
  | add (a b : DynExpr 𝕋)
  | sub (a b : DynExpr 𝕋)
  | mul (a b : DynExpr 𝕋)
  | div (a b : DynExpr 𝕋)
  | neg (a : DynExpr 𝕋)
  | sin (a : DynExpr 𝕋)
  | cos (a : DynExpr 𝕋)
  | exp (a : DynExpr 𝕋)
  | sqrt (a : DynExpr 𝕋)
  | log (a : DynExpr 𝕋)
  | tan (a : DynExpr 𝕋)
  | atan (a : DynExpr 𝕋)
  | pow (a : DynExpr 𝕋) (k : Int)

section
variable {𝕋 : Type} [FloatOps 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `a + b`, a zero summand dropped. -/
private def aux_add : DynExpr 𝕋 → DynExpr 𝕋 → DynExpr 𝕋
  | .zero, b => b
  | a, .zero => a
  | a, b => .add a b

/-- `a - b`, a zero operand dropped. -/
private def aux_sub : DynExpr 𝕋 → DynExpr 𝕋 → DynExpr 𝕋
  | a, .zero => a
  | .zero, b => .neg b
  | a, b => .sub a b

/-- `a * b`, a zero factor a zero, a one factor dropped. -/
private def aux_mul : DynExpr 𝕋 → DynExpr 𝕋 → DynExpr 𝕋
  | .zero, _ => .zero
  | _, .zero => .zero
  | .one, b => b
  | a, .one => a
  | a, b => .mul a b

/-- The derivative of the tree `e` by the variable `v`: `x_i` is variable `i`, `u_j` variable
`n + j`. -/
private def aux_diff (n v : Nat) : DynExpr 𝕋 → DynExpr 𝕋
  | .zero | .one | .const _ => .zero
  | .x i => if i = v then .one else .zero
  | .u j => if n + j = v then .one else .zero
  | .add a b => aux_add (aux_diff n v a) (aux_diff n v b)
  | .sub a b => aux_sub (aux_diff n v a) (aux_diff n v b)
  | .mul a b => aux_add (aux_mul (aux_diff n v a) b) (aux_mul a (aux_diff n v b))
  | .div a b => .div (aux_sub (aux_mul (aux_diff n v a) b) (aux_mul a (aux_diff n v b))) (.pow b 2)
  | .neg a => .neg (aux_diff n v a)
  | .sin a => aux_mul (.cos a) (aux_diff n v a)
  | .cos a => .neg (aux_mul (.sin a) (aux_diff n v a))
  | .exp a => aux_mul (.exp a) (aux_diff n v a)
  | .sqrt a => .div (aux_diff n v a) (.mul (.const (nsmulUp 2 FloatOps.one)) (.sqrt a))
  | .log a => .div (aux_diff n v a) a
  | .tan a => aux_mul (.add .one (.pow (.tan a) 2)) (aux_diff n v a)
  | .atan a => .div (aux_diff n v a) (.add .one (.pow a 2))
  | .pow a k =>
    -- `k a^(k-1) a'`, the coefficient the integer `k` as a float (exact for small `k`)
    let c : 𝕋 := if 0 ≤ k then nsmulUp k.toNat FloatOps.one
      else FloatOps.neg (nsmulUp (-k).toNat FloatOps.one)
    if k = 0 then .zero else aux_mul (aux_mul (.const c) (.pow a (k - 1))) (aux_diff n v a)

/-- The interval natural extension of the tree over the boxes `X`, `U`, with the elementary
functions tuned by `p`; the result is a box of dimension 1. -/
private def aux_eval {n m : Nat} (p : Nat) (X : Interval (Vec 𝕋 n)) (U : Interval (Vec 𝕋 m)) :
    DynExpr 𝕋 → Interval (Vec 𝕋 1)
  | .zero => Interval.point fun _ => FloatOps.zero
  | .one => Interval.point fun _ => FloatOps.one
  | .const c => Interval.point fun _ => c
  | .x i => if h : i < n then ⟨fun _ => X.inf ⟨i, h⟩, fun _ => X.sup ⟨i, h⟩⟩
    else Interval.point fun _ => FloatOps.zero
  | .u j => if h : j < m then ⟨fun _ => U.inf ⟨j, h⟩, fun _ => U.sup ⟨j, h⟩⟩
    else Interval.point fun _ => FloatOps.zero
  | .add a b => Interval.plus (aux_eval p X U a) (aux_eval p X U b)
  | .sub a b => Interval.minus (aux_eval p X U a) (aux_eval p X U b)
  | .mul a b => Interval.times (aux_eval p X U a) (aux_eval p X U b)
  | .div a b => Interval.rdivide (aux_eval p X U a) (aux_eval p X U b)
  | .neg a => Interval.uminus (aux_eval p X U a)
  | .sin a => Interval.sin p (aux_eval p X U a)
  | .cos a => Interval.cos p (aux_eval p X U a)
  | .exp a => Interval.exp p (aux_eval p X U a)
  | .sqrt a => Interval.sqrt p (aux_eval p X U a)
  | .log a => Interval.log p p (aux_eval p X U a)
  | .atan a => Interval.atan p p (aux_eval p X U a)
  -- a `tan` not certified bounded poisons its box with a NaN, which no interval op absorbs
  | .tan a =>
    let E := Interval.tan p (aux_eval p X U a)
    ⟨fun _ => (E.lo 0).getD (FloatOps.divUp FloatOps.zero FloatOps.zero),
      fun _ => (E.hi 0).getD (FloatOps.divUp FloatOps.zero FloatOps.zero)⟩
  | .pow a k =>
    -- a negative exponent is the reciprocal of the positive power
    if 0 ≤ k then Interval.power (aux_eval p X U a) k.toNat
    else Interval.rdivide (Interval.point fun _ => FloatOps.one)
      (Interval.power (aux_eval p X U a) (-k).toNat)

/-- The box `[0, 0]`, the stand-in for an entry outside a table. -/
private def aux_zeroBox : Interval (Vec 𝕋 1) := Interval.point fun _ => FloatOps.zero

/-- The `FloatHessModel` of the field `f`: its tree evaluated for the field, its first and its
second derivatives for the Jacobian and Hessian boxes. Each call evaluates every entry once. -/
private def aux_model (p n m : Nat) (f : Fin n → DynExpr 𝕋) : NonlinearSys.FloatHessModel 𝕋 n m :=
  -- the derivative trees, built once, as tables indexed by the variables
  let d1 : Array (Array (DynExpr 𝕋)) :=
    Array.ofFn fun (i : Fin n) => Array.ofFn fun (a : Fin (n + m)) => aux_diff n a (f i)
  let d2 : Array (Array (Array (DynExpr 𝕋))) := d1.map fun row => row.map fun e =>
    Array.ofFn fun (b : Fin (n + m)) => aux_diff n b e
  -- the boxes of one row of trees over `X`, `U`, and an entry of a row of boxes
  let evalRow := fun (X : Interval (Vec 𝕋 n)) (U : Interval (Vec 𝕋 m)) (es : Array (DynExpr 𝕋)) =>
    es.map (aux_eval p X U)
  let entry := fun (r : Array (Interval (Vec 𝕋 1))) (j : Nat) => r.getD j aux_zeroBox
  -- the model: each field evaluates its table once per call
  { f := fun X U =>
      let r := Array.ofFn fun (i : Fin n) => aux_eval p X U (f i)
      ⟨fun i => (entry r i).inf 0, fun i => (entry r i).sup 0⟩
    jacX := fun X U =>
      let T := d1.map (evalRow X U)
      ⟨fun i j => (entry (T.getD i #[]) j).inf 0, fun i j => (entry (T.getD i #[]) j).sup 0⟩
    -- the input columns come after the `n` state columns
    jacU := fun X U =>
      let T := d1.map (evalRow X U)
      ⟨fun i j => (entry (T.getD i #[]) (n + j)).inf 0,
        fun i j => (entry (T.getD i #[]) (n + j)).sup 0⟩
    -- the Hessian box of component `i` over the joint variables
    hess := fun X U i =>
      let T := (d2.getD i #[]).map (·.map (aux_eval p X U))
      ⟨fun a b => (entry (T.getD a #[]) b).inf 0, fun a b => (entry (T.getD a #[]) b).sup 0⟩ }

-- (the tables of `aux_model` are read by row, then by column; a missing entry reads as `[0, 0]`)

/-- A tree from its JSON: a leaf `{"x":i}`, `{"u":j}`, `{"const":scalar}`, or
`{"op":name,"args":[...]}` (`pow` with `"exponent"`). -/
private partial def aux_parse (dops : DtypeOps 𝕋) (n m : Nat) (j : Json) :
    Except String (DynExpr 𝕋) := do
  match fieldOpt j "x", fieldOpt j "u", fieldOpt j "const" with
  | some _, _, _ =>
    let i ← natField j "x"
    if i < n then pure (.x i) else throw s!"variable x_{i} with only {n} states"
  | _, some _, _ =>
    let k ← natField j "u"
    if k < m then pure (.u k) else throw s!"input u_{k} with only {m} inputs"
  | _, _, some _ => pure (.const (← dops.readExact "const" (← scalarField j "const")))
  | none, none, none =>
    let op ← strField j "op"
    let args ← (← arrField j "args").mapM (aux_parse dops n m)
    -- the arithmetic, then the functions of one argument
    match op, args.toList with
    | "add", [a, b] => pure (.add a b)
    | "sub", [a, b] => pure (.sub a b)
    | "mul", [a, b] => pure (.mul a b)
    | "div", [a, b] => pure (.div a b)
    | "neg", [a] => pure (.neg a)
    -- an integer power takes its exponent beside the argument
    | "sin", [a] => pure (.sin a)
    | "cos", [a] => pure (.cos a)
    | "exp", [a] => pure (.exp a)
    | "sqrt", [a] => pure (.sqrt a)
    | "log", [a] => pure (.log a)
    | "atan", [a] => pure (.atan a)
    | "pow", [a] =>
      match (← field j "exponent").getInt? with
      | .ok k => pure (.pow a k)
      | .error _ => throw "pow: `exponent` must be an integer"
    | "tan", [a] => pure (.tan a)
    | _, _ => throw s!"unknown operation `{op}` or wrong number of arguments"

/-- Whether the tree has a `tan` node. -/
private def aux_hasTan : DynExpr 𝕋 → Bool
  | .tan _ => true
  | .add a b | .sub a b | .mul a b | .div a b => aux_hasTan a || aux_hasTan b
  | .neg a | .sin a | .cos a | .exp a | .sqrt a | .log a | .atan a | .pow a _ => aux_hasTan a
  | _ => false

/-- `a` as an exact fraction. -/
private def aux_ratOf : ExactScalar → ℚ
  | .dy ⟨m, e⟩ => if e ≥ 0 then (m * 2 ^ e.toNat : ℤ) else (m : ℚ) / (2 ^ (-e).toNat : ℕ)
  | .decNeg m d => (m : ℚ) / (10 ^ d : ℕ)

end

section
variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The model, the algorithm and the options shared by the two ops. -/
private def aux_setup (dops : DtypeOps 𝕋) (req : Json) :
    Except String (Σ n m : Nat, NonlinearSys.FloatHessModel 𝕋 n m × NonlinearSys.LinReachAlg ×
      LinearSys.ReachFloatOptions 𝕋) := do
  -- the dimensions, the field and the tuning
  let n ← natField req "n"
  let m ← natField req "m"
  let fs ← (← arrField req "f").mapM (aux_parse dops n m)
  if h : fs.size = n then
    let f : Fin n → DynExpr 𝕋 := fun i => fs[i.val]'(h ▸ i.isLt)
    -- an unbounded `tan` is a NaN in the result, so the dtype must have one
    if fs.any aux_hasTan && !ToRat.isNaN (FloatOps.divUp (FloatOps.zero : 𝕋) FloatOps.zero) then
      throw "tan: this dtype has no NaN to mark an unbounded enclosure; use a float dtype"
    let alg ← match fieldOpt req "alg" with
      | none => pure NonlinearSys.LinReachAlg.lin
      | some j => match j.getStr?.toOption with
        | some "lin" => pure NonlinearSys.LinReachAlg.lin
        | some "poly" => pure (NonlinearSys.LinReachAlg.poly (← natField req "errorOrder"))
        | _ => throw "`alg` must be `lin` or `poly`"
    let Δt ← dops.readExact "timeStep" (← scalarField req "timeStep")
    pure ⟨n, m, aux_model (← natField req "p") n m f, alg,
      { Δt := Δt, η := ← natField req "taylorTerms", ρ := ← natField req "zonotopeOrder" }⟩
  else throw s!"`f` has {fs.size} components, expected n = {n}"

/-- The linear step of the request's `linearStep`, `reachFloatInput` when absent. -/
private def aux_linearStep (req : Json) : Except String NonlinearSys.LinearStep :=
  match fieldOpt req "linearStep" with
  | none => pure .reachFloatInput
  | some j => match j.getStr?.toOption with
    | some "reachFloatInput" => pure .reachFloatInput
    | some "closedForm" => pure .closedForm
    | _ => throw "`linearStep` must be `reachFloatInput` or `closedForm`"

/-- The error for a result holding a NaN: only `tan`'s poison can put one there. -/
private def aux_tanMsg : String :=
  "the enclosure of `tan` is unbounded on a box of the run (a pole may lie in it)"

/-- The input set, the origin of the input space when absent. -/
private def aux_input (dops : DtypeOps 𝕋) (req : Json) (m : Nat) :
    Except String (Zonotope (Vec 𝕋 m)) :=
  match fieldOpt req "U" with
  | some j => parseZonotopeFixed dops.readExact m j
  | none => pure (Zonotope.origin m)

/-- `nonlinearSys.linReach`: one step of `FloatHessModel.linReachFloat` from `R`. -/
def handleNonlinearLinReach (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  dops.requireUnguaranteed "nonlinearSys.linReach"
  checkFields "linReach" req ["n", "m", "f", "p", "alg", "errorOrder", "R", "U", "timeStep",
    "taylorTerms", "zonotopeOrder", "linearStep"]
  let ⟨n, m, fm, alg, options⟩ ← aux_setup dops req
  let R ← parseZonotopeFixed dops.readExact n (← field req "R")
  match fm.linReachFloat alg (← aux_input dops req m) options R (← aux_linearStep req) with
  | none => throw "linReach: the region check, the order search or the linear step failed"
  | some (Rti, Rtp) =>
    if !noNaN (𝕋 := 𝕋) (Rti, Rtp) then throw aux_tanMsg
    else pure [("timeInterval", printZonotope dops.showExact Rti),
      ("timePoint", printZonotope dops.showExact Rtp)]

/-- `nonlinearSys.reach`: `FloatHessModel.reachAlgFloat`, the windows of every step. -/
def handleNonlinearReach (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  dops.requireUnguaranteed "nonlinearSys.reach"
  checkFields "reach" req ["n", "m", "f", "p", "alg", "errorOrder", "X0", "U", "tStart", "tFinal",
    "timeStep", "taylorTerms", "zonotopeOrder"]
  let ⟨n, m, fm, alg, options⟩ ← aux_setup dops req
  let X0 ← parseZonotopeFixed dops.readExact n (← field req "X0")
  let tStart := match fieldOpt req "tStart" with
    | none => (0 : ℚ)
    | some _ => 0
  let tStart ← match fieldOpt req "tStart" with
    | none => pure tStart
    | some _ => pure (aux_ratOf (← scalarField req "tStart"))
  let params : Reach.InputParams (Zonotope (Vec 𝕋 n)) (Zonotope (Vec 𝕋 m)) ℚ :=
    { X₀ := X0, U := ← aux_input dops req m, tStart := tStart,
      tFinal := aux_ratOf (← scalarField req "tFinal") }
  match fm.reachAlgFloat alg params options with
  | none => throw "reach: a step failed, or (tFinal - tStart)/timeStep is not a natural number"
  | some Rs =>
    if !noNaN (𝕋 := 𝕋) Rs then throw aux_tanMsg
    else pure [("timeInterval", Json.arr (Rs.toArray.map (printZonotope dops.showExact)))]


/-- A scalar of the request, or the exact dyadic `m·2^e` (CORA's double) when absent. -/
private def aux_scalarOr (dops : DtypeOps 𝕋) (req : Json) (name : String) (m e : Int) :
    Except String 𝕋 :=
  match fieldOpt req name with
  | some _ => do dops.readExact name (← scalarField req name)
  | none => dops.readExact name (.dy ⟨m, e⟩)

/-- A natural number of the request, or `d` when absent. -/
private def aux_natOr (req : Json) (name : String) (d : Nat) : Except String Nat :=
  match fieldOpt req name with
  | some _ => natField req name
  | none => pure d

/-- The `lin-adaptive` options: the request's, else CORA's (`postProcessing`, the literals of
`linReach_adaptive`); `redFactor` defaults to CORA's `0.0005`. -/
private def aux_adaptiveOptions (dops : DtypeOps 𝕋) (req : Json) (poly : Bool := false) :
    Except String (NonlinearSys.LinReachAdaptiveOptions 𝕋) := do
  let rat := fun (name : String) (d : ℚ) => match fieldOpt req name with
    | some _ => do pure (aux_ratOf (← scalarField req name))
    | none => pure d
  let zetaphi ← match fieldOpt req "zetaphi" with
    | some _ => do
      let v ← parseVecFixed dops.readExact 3 (← field req "zetaphi")
      pure v
    | none => do
      -- `'lin'`: [0.85; 0.76; 0.68], `'poly'`: [0.80; 0.75; 0.63]
      let z1 ← dops.readExact "zetaphi" (.dy (if poly then ⟨3602879701896397, -52⟩
        else ⟨7656119366529843, -53⟩))
      let z2 ← dops.readExact "zetaphi" (.dy (if poly then ⟨3, -2⟩ else ⟨3422735716801577, -52⟩))
      let z3 ← dops.readExact "zetaphi" (.dy (if poly then ⟨5674535530486825, -53⟩
        else ⟨6124895493223875, -53⟩))
      pure ![z1, z2, z3]
  -- every field: the request's, else CORA's double
  pure {
    tStart := ← rat "tStart" 0,
    tFinal := ← rat "tFinal" 0,
    taylorTerms := ← aux_natOr req "taylorTerms" 10,
    zonotopeOrder := ← aux_natOr req "zonotopeOrder" 1000,
    -- the constants of `postProcessing` and the literals of `linReach_adaptive`
    redFactor := ← aux_scalarOr dops req "redFactor"
      (if poly then 7378697629483821 else 1152921504606847) (if poly then -66 else -61),
    decrFactor := ← aux_scalarOr dops req "decrFactor" 8106479329266893 (-53),
    zetaphi := zetaphi,
    zetaK := ← aux_scalarOr dops req "zetaK" 8106479329266893 (-53),
    initFactor := ← aux_scalarOr dops req "initFactor" 5764607523034235 (-59),
    enlarge := ← aux_scalarOr dops req "enlarge" 2476979795053773 (-51),
    horizonTol := ← aux_scalarOr dops req "horizonTol" 1152921504606847 (-60),
    zeroTol := ← aux_scalarOr dops req "zeroTol" 3022314549036573 (-78),
    varphiTol := ← aux_scalarOr dops req "varphiTol" 4835703278458517 (-82),
    varphiStep := ← aux_scalarOr dops req "varphiStep" 4722366482869645 (-72),
    endTol := ← aux_scalarOr dops req "endTol" 4951760157141521 (-92),
    abortRatio := ← aux_scalarOr dops req "abortRatio" 1000000000 0,
    prec := ← natField req "p",
    fuel := ← aux_natOr req "fuel" 10000,
    linearStep := ← aux_linearStep req }

/-- The option fields every adaptive op accepts. -/
private def aux_adaptiveFields : List String :=
  ["tStart", "tFinal", "taylorTerms", "zonotopeOrder", "redFactor", "decrFactor", "zetaphi",
    "zetaK", "initFactor", "enlarge", "horizonTol", "zeroTol", "varphiTol", "varphiStep",
    "endTol", "abortRatio", "fuel", "linearStep"]

/-- The model of the request's dynamics tree. -/
private def aux_adaptiveModel (dops : DtypeOps 𝕋) (req : Json) :
    Except String (Σ n m : Nat, NonlinearSys.FloatHessModel 𝕋 n m) := do
  let n ← natField req "n"
  let m ← natField req "m"
  let fs ← (← arrField req "f").mapM (aux_parse dops n m)
  if h : fs.size = n then
    if fs.any aux_hasTan then throw "tan: not served by the adaptive ops"
    pure ⟨n, m, aux_model (← natField req "p") n m fun i => fs[i.val]'(h ▸ i.isLt)⟩
  else throw s!"`f` has {fs.size} components, expected n = {n}"

/-- A dyadic rational as a wire scalar; a non-dyadic one is refused. -/
private def aux_showRat (q : ℚ) : Except String String :=
  let d := q.den
  if d &&& (d - 1) = 0 then
    pure (showExactDyadic ⟨q.num, -((Nat.log2 d : Nat) : Int)⟩)
  else throw s!"time {q} is not dyadic"

/-- An array of booleans of length `n`. -/
private def aux_boolsField (req : Json) (name : String) (n : Nat) :
    Except String (Fin n → Bool) := do
  let a ← arrField req name
  if a.size ≠ n then throw s!"`{name}` has {a.size} entries, expected {n}"
  let bs ← a.mapM fun j => match j.getBool? with
    | .ok b => pure b
    | .error _ => throw s!"`{name}` must hold booleans"
  pure fun i => bs.getD i.val false

/-- The state fields of a request (absent ones as `linReachAdaptiveInit` sets them). -/
private def aux_parseAdaptiveState (dops : DtypeOps 𝕋) (o : NonlinearSys.LinReachAdaptiveOptions 𝕋)
    (n : Nat) (req : Json) : Except String (NonlinearSys.LinReachAdaptiveState 𝕋 n) := do
  let R ← parseZonotopeFixed dops.readExact n (← field req "R")
  let s₀ := NonlinearSys.linReachAdaptiveInit o R
  let sc := fun (name : String) (d : 𝕋) => match fieldOpt req name with
    | some _ => do dops.readExact name (← scalarField req name)
    | none => pure d
  let vec := fun (name : String) (d : Vec 𝕋 n) => match fieldOpt req name with
    | some _ => do parseVecFixed dops.readExact n (← field req name)
    | none => pure d
  let orders ← match fieldOpt req "orders" with
    | none => pure s₀.orders
    | some _ => do
      let a ← arrField req "orders"
      if a.size ≠ n then throw s!"`orders` has {a.size} entries, expected {n}"
      let os ← a.mapM fun j => if j.isNull then pure none else match j.getNat? with
        | .ok k => pure (some k)
        | .error _ => throw "`orders` must hold naturals or null (Inf)"
      pure fun i => os.getD i.val none
  -- the step sizes so far, latest first
  let steps ← match fieldOpt req "steps" with
    | none => pure []
    | some _ => do
      let a ← arrField req "steps"
      (a.toList.mapM fun j => do
        let x ← match j.getStr? with
          | .ok _ => pure (← scalarField (Json.mkObj [("x", j)]) "x")
          | .error _ => throw "`steps` must hold scalars"
        dops.readExact "steps" x)
  -- the fields the request gives, the rest as at the first step
  pure { s₀ with
    i := ← aux_natOr req "i" 1,
    t := match fieldOpt req "t" with
      | some _ => match scalarField req "t" with
        | .ok x => aux_ratOf x
        | .error _ => o.tStart
      | none => o.tStart,
    timeStep := ← sc "timeStep" s₀.timeStep,
    finitehorizon := ← sc "finitehorizon" s₀.finitehorizon,
    varphi := ← sc "varphi" s₀.varphi,
    -- the admissible errors, the tensor order and the orders
    errAdmHorizon := ← vec "errAdmHorizon" s₀.errAdmHorizon,
    errAdmDeltatopt := ← vec "errAdmDeltatopt" s₀.errAdmDeltatopt,
    tensorOrder := ← aux_natOr req "tensorOrder" 2,
    orders := orders,
    minorder := ← aux_natOr req "minorder" 0,
    zeroWidthDim := ← match fieldOpt req "zeroWidthDim" with
      | some _ => aux_boolsField req "zeroWidthDim" n
      | none => pure s₀.zeroWidthDim,
    kappaDeltat := ← sc "kappaDeltat" s₀.kappaDeltat,
    kappaAbstrerr := ← sc "kappaAbstrerr" s₀.kappaAbstrerr,
    steps := steps }

/-- The state as response fields: the sets as `timePoint` and `timeInterval`. -/
private def aux_printAdaptiveState (dops : DtypeOps 𝕋) {n : Nat}
    (s : NonlinearSys.LinReachAdaptiveState 𝕋 n) : Except String (List (String × Json)) := do
  pure [("i", Lean.toJson s.i), ("t", Json.str (← aux_showRat s.t)),
    ("timePoint", printZonotope dops.showExact s.R),
    ("timeInterval", printZonotope dops.showExact s.Rτ),
    ("timeStep", Json.str (dops.showExact s.timeStep)),
    ("finitehorizon", Json.str (dops.showExact s.finitehorizon)),
    ("varphi", Json.str (dops.showExact s.varphi)),
    -- the tuning state
    ("errAdmHorizon", printVec dops.showExact s.errAdmHorizon),
    ("errAdmDeltatopt", printVec dops.showExact s.errAdmDeltatopt),
    ("tensorOrder", Lean.toJson s.tensorOrder),
    ("orders", Json.arr (Array.ofFn fun i : Fin n => match s.orders i with
      | some k => Lean.toJson k
      | none => Json.null)),
    ("minorder", Lean.toJson s.minorder),
    ("zeroWidthDim", Json.arr (Array.ofFn fun i : Fin n => Json.bool (s.zeroWidthDim i))),
    ("kappaDeltat", Json.str (dops.showExact s.kappaDeltat)),
    ("kappaAbstrerr", Json.str (dops.showExact s.kappaAbstrerr)),
    ("steps", Json.arr (s.steps.toArray.map fun x => Json.str (dops.showExact x)))]

/-- `nonlinearSys.reachAdaptive`: `FloatHessModel.reachAdaptiveFloat` from `R0`, at most `maxSteps`
steps: the step sizes and tensor orders, the last time-point set, and every time-interval set when
`sets` is true. -/
def handleNonlinearReachAdaptive (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  dops.requireUnguaranteed "nonlinearSys.reachAdaptive"
  checkFields "reachAdaptive" req (["n", "m", "f", "p", "R0", "U", "maxSteps", "sets"] ++
    aux_adaptiveFields)
  let ⟨n, m, fm⟩ ← aux_adaptiveModel dops req
  let o ← aux_adaptiveOptions dops req
  let R0 ← parseZonotopeFixed dops.readExact n (← field req "R0")
  let U ← aux_input dops req m
  -- the run, and the sets when asked for
  let sets := match fieldOpt req "sets" with
    | some j => j.getBool?.toOption.getD false
    | none => false
  match fm.reachAdaptiveFloat U o (← aux_natOr req "maxSteps" 1000000)
      (NonlinearSys.linReachAdaptiveInit o R0) with
  | none => throw "reachAdaptive: a step's loop ran out of fuel"
  | some ss =>
    let last := (ss.getLast?).getD (NonlinearSys.linReachAdaptiveInit o R0)
    pure ([("steps", Json.arr (ss.toArray.map fun s => Json.str (dops.showExact s.timeStep))),
      ("tensorOrders", Json.arr (ss.toArray.map fun s => Lean.toJson s.tensorOrder)),
      ("t", Json.str (← aux_showRat last.t)),
      ("timePoint", printZonotope dops.showExact last.R)] ++
      (if sets then [("timeInterval", Json.arr (ss.toArray.map fun s =>
        printZonotope dops.showExact s.Rτ))] else []))

/-- `nonlinearSys.linReachAdaptive`: one step `FloatHessModel.linReachAdaptiveFloat` from the
state of the request, the state after it (sets unreduced). -/
def handleNonlinearLinReachAdaptive (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  dops.requireUnguaranteed "nonlinearSys.linReachAdaptive"
  checkFields "linReachAdaptive" req (["n", "m", "f", "p", "U", "R", "i", "t", "timeStep",
    "finitehorizon", "varphi", "errAdmHorizon", "errAdmDeltatopt", "tensorOrder", "orders",
    "minorder", "zeroWidthDim", "kappaDeltat", "kappaAbstrerr", "steps"] ++ aux_adaptiveFields)
  let ⟨n, m, fm⟩ ← aux_adaptiveModel dops req
  let o ← aux_adaptiveOptions dops req
  let st ← aux_parseAdaptiveState dops o n req
  match fm.linReachAdaptiveFloat (← aux_input dops req m) o st with
  | none => throw "linReachAdaptive: the step's loop ran out of fuel"
  | some s => aux_printAdaptiveState dops s

/-- `nonlinearSys.linReachAdaptivePass`: `FloatHessModel.linReachAdaptivePassFloat`, one pass at
`timeStep` from `R` and `errorAdm`. -/
def handleNonlinearLinReachAdaptivePass (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  dops.requireUnguaranteed "nonlinearSys.linReachAdaptivePass"
  checkFields "linReachAdaptivePass" req ["n", "m", "f", "p", "U", "R", "timeStep", "taylorTerms",
    "zonotopeOrder", "tensorOrder", "errorAdm", "redFactor", "enlarge", "fuel", "linearStep"]
  let ⟨n, m, fm⟩ ← aux_adaptiveModel dops req
  let o ← aux_adaptiveOptions dops req
  let R ← parseZonotopeFixed dops.readExact n (← field req "R")
  let opts : LinearSys.ReachFloatOptions 𝕋 :=
    ⟨⟨← dops.readExact "timeStep" (← scalarField req "timeStep"), o.taylorTerms⟩, o.zonotopeOrder⟩
  let e ← parseVecFixed dops.readExact n (← field req "errorAdm")
  -- one pass, and what the tuning reads of it
  match fm.linReachAdaptivePassFloat (← aux_natOr req "tensorOrder" 2) (← aux_input dops req m)
      opts o.enlarge o.redFactor o.prec o.fuel R e o.linearStep with
  | none => throw "linReachAdaptivePass: the abstraction-error loop did not converge"
  | some P => pure [("timeInterval", printZonotope dops.showExact P.Rti),
      ("timePoint", printZonotope dops.showExact P.Rtp), ("A", printMat dops.showExact P.A),
      ("xs", printVec dops.showExact P.xs), ("Rmax", printZonotope dops.showExact P.Rmax),
      ("trueError", printVec dops.showExact P.trueError),
      ("abstrerr", printVec dops.showExact P.abstrerr),
      ("Gzero", Json.arr (Array.ofFn fun i : Fin n => Json.bool (P.Gzero i)))]

/-- The `poly-adaptive` options: the `lin-adaptive` ones at `'poly'`'s defaults, and `dHused`
(`0.3`), `thirdOrderEmpty` (`false`) and `maxDepGenOrder` (`50`). -/
private def aux_polyOptions (dops : DtypeOps 𝕋) (req : Json) :
    Except String (NonlinearSys.LinReachPolyAdaptiveOptions 𝕋) := do
  pure { toLinReachAdaptiveOptions := ← aux_adaptiveOptions dops req (poly := true),
         dHused := ← aux_scalarOr dops req "dHused" 5404319552844595 (-54),
         thirdOrderEmpty := match fieldOpt req "thirdOrderEmpty" with
           | some j => j.getBool?.toOption.getD false
           | none => false,
         maxDepGenOrder := ← aux_natOr req "maxDepGenOrder" 50 }

/-- The option fields every poly-adaptive op accepts. -/
private def aux_polyFields : List String :=
  ["tStart", "tFinal", "taylorTerms", "zonotopeOrder", "redFactor", "decrFactor", "zetaphi",
    "zetaK", "initFactor", "enlarge", "horizonTol", "zeroTol", "varphiTol", "varphiStep",
    "endTol", "abortRatio", "fuel", "dHused", "thirdOrderEmpty", "maxDepGenOrder",
    "maxPolyZonoRatio"]

/-- The `poly-adaptive` state of a request: the fields it gives, the rest as at the first step. -/
private def aux_parsePolyState (dops : DtypeOps 𝕋) (o : NonlinearSys.LinReachPolyAdaptiveOptions 𝕋)
    (n : Nat) (req : Json) : Except String (NonlinearSys.LinReachPolyAdaptiveState 𝕋 n) := do
  let R ← parsePolyZonotopeFixed dops.readExact n (← field req "R")
  let s₀ := NonlinearSys.linReachPolyAdaptiveInit o R
  -- a scalar or vector of the request, else the first step's value
  let sc := fun (name : String) (d : 𝕋) => match fieldOpt req name with
    | some _ => do dops.readExact name (← scalarField req name)
    | none => pure d
  let vec := fun (name : String) (d : Vec 𝕋 n) => match fieldOpt req name with
    | some _ => do parseVecFixed dops.readExact n (← field req name)
    | none => pure d
  -- the orders `q_i`, `null` for `Inf`
  let orders ← match fieldOpt req "orders" with
    | none => pure s₀.orders
    | some _ => do
      let a ← arrField req "orders"
      if a.size ≠ n then throw s!"`orders` has {a.size} entries, expected {n}"
      let os ← a.mapM fun j => if j.isNull then pure none else match j.getNat? with
        | .ok k => pure (some k)
        | .error _ => throw "`orders` must hold naturals or null (Inf)"
      pure fun i => os.getD i.val none
  -- the step sizes so far, latest first
  let steps ← match fieldOpt req "steps" with
    | none => pure []
    | some _ => do
      (← arrField req "steps").toList.mapM fun j => do
        match j.getStr? with
        | .ok _ => dops.readExact "steps" (← scalarField (Json.mkObj [("x", j)]) "x")
        | .error _ => throw "`steps` must hold scalars"
  -- the fields the request gives, the rest as at the first step
  pure { s₀ with
    i := ← aux_natOr req "i" 1,
    t := match fieldOpt req "t" with
      | some _ => match scalarField req "t" with
        | .ok x => aux_ratOf x
        | .error _ => o.tStart
      | none => o.tStart,
    timeStep := ← sc "timeStep" s₀.timeStep,
    finitehorizon := ← sc "finitehorizon" s₀.finitehorizon,
    varphi := ← sc "varphi" s₀.varphi,
    errAdmHorizon := ← vec "errAdmHorizon" s₀.errAdmHorizon,
    errAdmDeltatopt := ← vec "errAdmDeltatopt" s₀.errAdmDeltatopt,
    orders := orders,
    minorder := ← aux_natOr req "minorder" 0,
    zeroWidthDim := ← match fieldOpt req "zeroWidthDim" with
      | some _ => aux_boolsField req "zeroWidthDim" n
      | none => pure s₀.zeroWidthDim,
    steps := steps }

/-- `nonlinearSys.linReachPolyAdaptive`: one step `FloatHessModel.linReachPolyAdaptiveFloat`
from the state of the request, the state after it (sets unreduced). -/
def handleNonlinearLinReachPolyAdaptive (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  dops.requireUnguaranteed "nonlinearSys.linReachPolyAdaptive"
  checkFields "linReachPolyAdaptive" req (["n", "m", "f", "p", "U", "R", "i", "t", "timeStep",
    "finitehorizon", "varphi", "errAdmHorizon", "errAdmDeltatopt", "orders", "minorder",
    "zeroWidthDim", "steps"] ++ aux_polyFields)
  let ⟨n, m, fm⟩ ← aux_adaptiveModel dops req
  let o ← aux_polyOptions dops req
  let st ← aux_parsePolyState dops o n req
  match fm.linReachPolyAdaptiveFloat (← aux_input dops req m) o st with
  | none => throw "linReachPolyAdaptive: the step's loop ran out of fuel"
  -- the state after the step, its sets unreduced
  | some s => pure [("i", Lean.toJson s.i), ("t", Json.str (← aux_showRat s.t)),
      ("timePoint", printPolyZonotope dops.showExact s.R),
      ("timeInterval", printPolyZonotope dops.showExact s.Rτ),
      ("timeStep", Json.str (dops.showExact s.timeStep)),
      ("finitehorizon", Json.str (dops.showExact s.finitehorizon)),
      ("varphi", Json.str (dops.showExact s.varphi)),
      ("errAdmHorizon", printVec dops.showExact s.errAdmHorizon),
      ("errAdmDeltatopt", printVec dops.showExact s.errAdmDeltatopt),
      ("orders", Json.arr (Array.ofFn fun i : Fin n => match s.orders i with
        | some k => Lean.toJson k
        | none => Json.null)),
      ("minorder", Lean.toJson s.minorder),
      ("zeroWidthDim", Json.arr (Array.ofFn fun i : Fin n => Json.bool (s.zeroWidthDim i))),
      ("steps", Json.arr (s.steps.toArray.map fun x => Json.str (dops.showExact x)))]

/-- `nonlinearSys.reachPolyAdaptive`: `FloatHessModel.reachPolyAdaptiveFloat` from `R0` (a
polynomial zonotope), at most `maxSteps` steps: the step sizes, the last time-point set, and every
time-interval set when `sets` is true. -/
def handleNonlinearReachPolyAdaptive (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  dops.requireUnguaranteed "nonlinearSys.reachPolyAdaptive"
  checkFields "reachPolyAdaptive" req (["n", "m", "f", "p", "R0", "U", "maxSteps", "sets"] ++
    aux_polyFields)
  let ⟨n, m, fm⟩ ← aux_adaptiveModel dops req
  let o ← aux_polyOptions dops req
  let R0 ← parsePolyZonotopeFixed dops.readExact n (← field req "R0")
  let U ← aux_input dops req m
  let ratio ← aux_scalarOr dops req "maxPolyZonoRatio" 3602879701896397 (-56)  -- 0.05
  let sets := match fieldOpt req "sets" with
    | some j => j.getBool?.toOption.getD false
    | none => false
  match fm.reachPolyAdaptiveFloat U o ratio (← aux_natOr req "maxSteps" 1000000)
      (NonlinearSys.linReachPolyAdaptiveInit o R0) with
  | none => throw "reachPolyAdaptive: a step's loop ran out of fuel"
  | some ss =>
    let last := (ss.getLast?).getD (NonlinearSys.linReachPolyAdaptiveInit o R0)
    pure ([("steps", Json.arr (ss.toArray.map fun s => Json.str (dops.showExact s.timeStep))),
      ("t", Json.str (← aux_showRat last.t)),
      ("timePoint", printPolyZonotope dops.showExact last.R)] ++
      (if sets then [("timeInterval", Json.arr (ss.toArray.map fun s =>
        printPolyZonotope dops.showExact s.Rτ))] else []))

/-- `nonlinearSys.linReachPolyAdaptivePass`: `FloatHessModel.linReachPolyAdaptivePassFloat`, one
pass at `timeStep` from the polynomial zonotope `R` and `errorAdm`. -/
def handleNonlinearLinReachPolyAdaptivePass (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  dops.requireUnguaranteed "nonlinearSys.linReachPolyAdaptivePass"
  checkFields "linReachPolyAdaptivePass" req ["n", "m", "f", "p", "U", "R", "timeStep",
    "taylorTerms", "zonotopeOrder", "errorAdm", "redFactor", "enlarge", "fuel"]
  let ⟨n, m, fm⟩ ← aux_adaptiveModel dops req
  let o ← aux_polyOptions dops req
  let R ← parsePolyZonotopeFixed dops.readExact n (← field req "R")
  let opts : LinearSys.ReachFloatOptions 𝕋 :=
    ⟨⟨← dops.readExact "timeStep" (← scalarField req "timeStep"), o.taylorTerms⟩, o.zonotopeOrder⟩
  let e ← parseVecFixed dops.readExact n (← field req "errorAdm")
  match fm.linReachPolyAdaptivePassFloat (← aux_input dops req m) opts o.enlarge o.redFactor
      o.prec o.fuel R e with
  | none => throw "linReachPolyAdaptivePass: the abstraction-error loop did not converge"
  | some P => pure [("timeInterval", printPolyZonotope dops.showExact P.Rti),
      ("timePoint", printPolyZonotope dops.showExact P.Rtp), ("A", printMat dops.showExact P.A),
      ("xs", printVec dops.showExact P.xs),
      ("trueError", printVec dops.showExact P.trueError),
      ("abstrerr", printVec dops.showExact P.abstrerr),
      ("Gzero", Json.arr (Array.ofFn fun i : Fin n => Json.bool (P.Gzero i)))]

/-- `nonlinearSys.abstrErrAdaptive`: `FloatHessModel.abstrErrAdaptiveFloat` for `Rmax` at the
linearization point `xs` (`A`, `B` the model's Jacobians there), and `trueError`. -/
def handleNonlinearAbstrErrAdaptive (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  dops.requireUnguaranteed "nonlinearSys.abstrErrAdaptive"
  checkFields "abstrErrAdaptive" req ["n", "m", "f", "p", "U", "xs", "Rmax", "tensorOrder",
    "redFactor"]
  let ⟨n, m, fm⟩ ← aux_adaptiveModel dops req
  let o ← aux_adaptiveOptions dops req
  let xs ← parseVecFixed dops.readExact n (← field req "xs")
  let Rmax ← parseZonotopeFixed dops.readExact n (← field req "Rmax")
  let U ← aux_input dops req m
  let AB := fm.toFloatModel.linearizeFloat xs U.c
  let V := fm.abstrErrAdaptiveFloat (← aux_natOr req "tensorOrder" 2) AB.1 AB.2 xs Rmax U
    o.redFactor o.prec
  pure [("VerrorDyn", printZonotope dops.showExact V),
    ("trueError", printVec dops.showExact V.interval.normMag)]

/-- `nonlinearSys.ordersAdaptive`: `NonlinearSys.adaptiveOrdersFloat`, the orders `q_i` (`null` for
`Inf`) from `A`, the zero-width dimensions, the zero rows of the error and the model's Hessian at
`xs`, `u✱ = center(U)`. -/
def handleNonlinearOrdersAdaptive (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  dops.requireUnguaranteed "nonlinearSys.ordersAdaptive"
  checkFields "ordersAdaptive" req ["n", "m", "f", "p", "U", "A", "xs", "zeroWidthDim", "Gzero"]
  let ⟨n, m, fm⟩ ← aux_adaptiveModel dops req
  let ⟨r, A⟩ ← parseMatColsFixed dops.readExact n (← field req "A")
  if h : r = n then
    let xs ← parseVecFixed dops.readExact n (← field req "xs")
    let U ← aux_input dops req m
    let q := NonlinearSys.adaptiveOrdersFloat (h ▸ A) (← aux_boolsField req "zeroWidthDim" n)
      (← aux_boolsField req "Gzero" n) (fm.hess (Interval.point xs) (Interval.point U.c)) 100
    pure [("orders", Json.arr (Array.ofFn fun i : Fin n => match q i with
      | some k => Lean.toJson k
      | none => Json.null))]
  else throw s!"`A` has {r} rows, expected n = {n}"

/-- `nonlinearSys.optimalDeltatAdaptive`: `NonlinearSys.optimalDeltatAdaptiveFloat`. -/
def handleNonlinearOptimalDeltatAdaptive (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  dops.requireUnguaranteed "nonlinearSys.optimalDeltatAdaptive"
  checkFields "optimalDeltatAdaptive" req ["p", "decrFactor", "redFactor", "rR", "rerr1", "deltat",
    "varphimin", "zetaP"]
  let o ← aux_adaptiveOptions dops req
  let sc := fun (name : String) => do dops.readExact name (← scalarField req name)
  valueScalar dops.showExact (NonlinearSys.optimalDeltatAdaptiveFloat o.prec o.decrFactor
    o.redFactor (← sc "rR") (← sc "rerr1") (← sc "deltat") (← sc "varphimin") (← sc "zetaP"))

/-- `nonlinearSys.varphiTotalAdaptive`: `NonlinearSys.varphiTotalFloat`. -/
def handleNonlinearVarphiTotalAdaptive (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  dops.requireUnguaranteed "nonlinearSys.varphiTotalAdaptive"
  checkFields "varphiTotalAdaptive" req ["p", "varphi", "varphiLim", "prev", "curr", "decrFactor"]
  let o ← aux_adaptiveOptions dops req
  let sc := fun (name : String) => do dops.readExact name (← scalarField req name)
  valueScalar dops.showExact (NonlinearSys.varphiTotalFloat o.prec (← sc "varphi")
    (← sc "varphiLim") (← sc "prev") (← sc "curr") o.decrFactor)

/-- `nonlinearSys.varphiEstAdaptive`: `NonlinearSys.varphiEstFloat`. -/
def handleNonlinearVarphiEstAdaptive (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  dops.requireUnguaranteed "nonlinearSys.varphiEstAdaptive"
  checkFields "varphiEstAdaptive" req ["n", "p", "horizon", "deltat", "abstrerrH", "abstrerr",
    "decrFactor", "mask", "minorder", "varphiTol", "varphiStep", "fuel"]
  let n ← natField req "n"
  let o ← aux_adaptiveOptions dops req
  let sc := fun (name : String) => do dops.readExact name (← scalarField req name)
  valueScalar dops.showExact (NonlinearSys.varphiEstFloat o.prec (← sc "horizon") (← sc "deltat")
    (← parseVecFixed dops.readExact n (← field req "abstrerrH"))
    (← parseVecFixed dops.readExact n (← field req "abstrerr")) o.decrFactor
    (← aux_boolsField req "mask" n) (← natField req "minorder") o.varphiTol o.varphiStep o.fuel)

/-- Every op of this file, without the `nonlinearSys.` prefix. -/
def nonlinearSysOpNames : List String := [ "linReach", "reach", "reachAdaptive",
  "reachPolyAdaptive", "linReachPolyAdaptive", "linReachPolyAdaptivePass",
  "linReachAdaptive", "linReachAdaptivePass", "abstrErrAdaptive", "optimalDeltatAdaptive",
  "varphiTotalAdaptive", "varphiEstAdaptive", "ordersAdaptive" ]

/-- `op` of `nonlinearSys.`, run; `none` for a name this file does not serve. -/
@[noinline, nospecialize]
def handleNonlinearSysOp (dops : DtypeOps 𝕋) (op : String) (req : Json) : Option Resp :=
  match op with
  | "linReach" => some (handleNonlinearLinReach dops req)
  | "reach" => some (handleNonlinearReach dops req)
  | "reachAdaptive" => some (handleNonlinearReachAdaptive dops req)
  | "reachPolyAdaptive" => some (handleNonlinearReachPolyAdaptive dops req)
  | "linReachPolyAdaptive" => some (handleNonlinearLinReachPolyAdaptive dops req)
  | "linReachPolyAdaptivePass" => some (handleNonlinearLinReachPolyAdaptivePass dops req)
  | "linReachAdaptive" => some (handleNonlinearLinReachAdaptive dops req)
  | "linReachAdaptivePass" => some (handleNonlinearLinReachAdaptivePass dops req)
  | "abstrErrAdaptive" => some (handleNonlinearAbstrErrAdaptive dops req)
  | "optimalDeltatAdaptive" => some (handleNonlinearOptimalDeltatAdaptive dops req)
  | "varphiTotalAdaptive" => some (handleNonlinearVarphiTotalAdaptive dops req)
  | "varphiEstAdaptive" => some (handleNonlinearVarphiEstAdaptive dops req)
  | "ordersAdaptive" => some (handleNonlinearOrdersAdaptive dops req)
  | _ => none

end

end CORALean.Oracle


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
