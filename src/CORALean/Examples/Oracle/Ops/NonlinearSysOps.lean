import CORALean.ContDynamics.NonlinearSys.Operations.LinReachFloat
import CORALean.ContDynamics.NonlinearSys.Operations.ReachAlgFloat
import CORALean.ContSet.Interval.Float.Operations.Basic
import CORALean.ContSet.Interval.Float.Operations.Cos
import CORALean.ContSet.Interval.Float.Operations.Power
import CORALean.ContSet.Interval.Float.Operations.Sin
import CORALean.ContSet.Interval.Float.Operations.Sqrt
import CORALean.ContSet.Interval.Float.Operations.Times
import CORALean.Examples.Oracle.Ops.SetCodec
import CORALean.Specification.Instances

/-!
# The nonlinear-system ops: CORA's `linReach` on a dynamics tree

The dynamics are an expression tree of the request, evaluated over boxes by the interval natural
extension and differentiated symbolically, which gives the `FloatHessModel` that `linReachFloat`
takes. The model's enclosure property is by construction, not checked in Lean; an operand outside
an elementary function's domain (a division by a box holding 0, `sqrt` of a negative box) is not
refused but evaluated by CORALean's definition. The tree and the ops are in
`experiments/oracle/README.md`. `tan` is not served, its bound can be infinite.

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
    | "pow", [a] =>
      match (← field j "exponent").getInt? with
      | .ok k => pure (.pow a k)
      | .error _ => throw "pow: `exponent` must be an integer"
    | "tan", _ => throw "tan is not served: its bound can be infinite, write sin/cos"
    | _, _ => throw s!"unknown operation `{op}` or wrong number of arguments"

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
      LinearSys.ReachOptions 𝕋) := do
  -- the dimensions, the field and the tuning
  let n ← natField req "n"
  let m ← natField req "m"
  let fs ← (← arrField req "f").mapM (aux_parse dops n m)
  if h : fs.size = n then
    let f : Fin n → DynExpr 𝕋 := fun i => fs[i.val]'(h ▸ i.isLt)
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

/-- The input set, the origin of the input space when absent. -/
private def aux_input (dops : DtypeOps 𝕋) (req : Json) (m : Nat) :
    Except String (Zonotope (Vec 𝕋 m)) :=
  match fieldOpt req "U" with
  | some j => parseZonotopeFixed dops.readExact m j
  | none => pure (Zonotope.origin m)

/-- `nonlinearSys.linReach`: one step of `FloatHessModel.linReachFloat` from `R`. -/
def handleNonlinearLinReach (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  checkFields "linReach" req ["n", "m", "f", "p", "alg", "errorOrder", "R", "U", "timeStep",
    "taylorTerms", "zonotopeOrder"]
  let ⟨n, m, fm, alg, options⟩ ← aux_setup dops req
  let R ← parseZonotopeFixed dops.readExact n (← field req "R")
  match fm.linReachFloat alg (← aux_input dops req m) options R with
  | none => throw "linReach: the region check, the order search or the linear step failed"
  | some (Rti, Rtp) => pure [("timeInterval", printZonotope dops.showExact Rti),
      ("timePoint", printZonotope dops.showExact Rtp)]

/-- `nonlinearSys.reach`: `FloatHessModel.reachAlgFloat`, the windows of every step. -/
def handleNonlinearReach (dops : DtypeOps 𝕋) (req : Json) : Resp := do
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
  | some Rs => pure [("timeInterval", Json.arr (Rs.toArray.map (printZonotope dops.showExact)))]

/-- Every op of this file, without the `nonlinearSys.` prefix. -/
def nonlinearSysOpNames : List String := [ "linReach", "reach" ]

/-- `op` of `nonlinearSys.`, run; `none` for a name this file does not serve. -/
@[noinline, nospecialize]
def handleNonlinearSysOp (dops : DtypeOps 𝕋) (op : String) (req : Json) : Option Resp :=
  match op with
  | "linReach" => some (handleNonlinearLinReach dops req)
  | "reach" => some (handleNonlinearReach dops req)
  | _ => none

end

end CORALean.Oracle


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
