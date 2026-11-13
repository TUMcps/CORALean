import CORALean.ContDynamics.NeurNetContrSys.Operations.Joint
import CORALean.ContDynamics.NeurNetContrSys.Operations.ReachNonlinFloat
import CORALean.Examples.Oracle.Ops.NnOps
import CORALean.Examples.Oracle.Ops.NonlinearSysOps
import CORALean.Examples.Oracle.Ops.SetCodec
import CORALean.ContDynamics.Reach.Operations.Steps
import CORALean.Global.Float.NoNaN

/-!
# The closed-loop op: CORA's `neurNetContrSys/reach` at a nonlinear plant

A control period joins the state set with the network's image of it (`aux_appendU2X`), runs the
augmented plant by `N = dt / timeStep` steps of CORA's `lin` error loop (`linReachLoopFloat`) and
projects the end set to the plant's states. The plant's tree is over `x_0 … x_{n-1}` and the
inputs `u_0 … u_{m+mExt-1}`, the first `m` of which the network drives. The network is the
request's `layers` at its `poly_method`, on the zonotope; the reply is the state sets at the ends
of the periods `1 … tFinal / dt`. Served at `nearest` only, as the other dynamics ops are.

## Inputs
* `dops` – dtype operations
* `req` – request

## Output
* response fields or an error message
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

/-- The plant's tree on the augmented system: the first `m` inputs are the states `x_{n+j}`, the
others the inputs `u_{j-m}`. -/
private def aux_closedLoop (n m : Nat) : DynExpr 𝕋 → DynExpr 𝕋
  | .zero => .zero
  | .one => .one
  | .const c => .const c
  | .x i => .x i
  | .u j => if j < m then .x (n + j) else .u (j - m)
  | .add a b => .add (aux_closedLoop n m a) (aux_closedLoop n m b)
  | .sub a b => .sub (aux_closedLoop n m a) (aux_closedLoop n m b)
  | .mul a b => .mul (aux_closedLoop n m a) (aux_closedLoop n m b)
  | .div a b => .div (aux_closedLoop n m a) (aux_closedLoop n m b)
  | .neg a => .neg (aux_closedLoop n m a)
  | .sin a => .sin (aux_closedLoop n m a)
  | .cos a => .cos (aux_closedLoop n m a)
  | .exp a => .exp (aux_closedLoop n m a)
  | .sqrt a => .sqrt (aux_closedLoop n m a)
  | .log a => .log (aux_closedLoop n m a)
  | .tan a => .tan (aux_closedLoop n m a)
  | .atan a => .atan (aux_closedLoop n m a)
  | .pow a k => .pow (aux_closedLoop n m a) k

/-- The network of the request on a state set, of `m` outputs. The request's layers were run on
the initial set before, so they parse and fit, and the fallback is not reached. -/
private def aux_network (dops : DtypeOps 𝕋) (req : Json) (n m : Nat) (X : Zonotope (Vec 𝕋 n)) :
    Zonotope (Vec 𝕋 m) :=
  match networkOnZonotope dops "neurNetContrSys.reach" req n X with
  | .ok ⟨k, Y⟩ => if h : k = m then h ▸ Y else Zonotope.origin m
  | .error _ => Zonotope.origin m


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `neurNetContrSys.reach`: `reachClosedLoopFloat` for `1 … tFinal / dt` periods. -/
def handleNeurNetContrSysReach (dops : DtypeOps 𝕋) (req : Json) : Resp := do
  dops.requireUnguaranteed "neurNetContrSys.reach"
  checkFields "reach" req ["n", "m", "mExt", "f", "p", "layers", "poly_method", "X0", "U", "dt",
    "tFinal", "timeStep", "taylorTerms", "zonotopeOrder", "linearStep", "enlarge", "fuel"]
  let n ← natField req "n"
  let m ← natField req "m"
  let e ← natOrDefault req "mExt" 0
  -- the plant's tree on the augmented system
  let fs ← (← arrField req "f").mapM (parseDynExpr dops n (m + e))
  if h : fs.size = n then
    if fs.any dynHasTan then throw "tan: not served by the closed-loop op"
    let f : Fin (n + m) → DynExpr 𝕋 := fun i =>
      if hi : i.val < n then aux_closedLoop n m (fs[i.val]'(h ▸ hi)) else .zero
    let fm := dynModel (← natField req "p") (n + m) e f
    -- the step, the period and the horizon, as natural numbers of steps
    let Δt ← dops.readExact "timeStep" (← scalarField req "timeStep")
    let options : LinearSys.ReachFloatOptions 𝕋 :=
      { Δt := Δt, η := ← natField req "taylorTerms", ρ := ← natField req "zonotopeOrder" }
    let dt := ratOfScalar (← scalarField req "dt")
    let tFinal := ratOfScalar (← scalarField req "tFinal")
    let some N := Reach.steps 0 dt (ToRat.toRat Δt)
      | throw "`dt` / `timeStep` is not a natural number"
    let some H := Reach.steps 0 tFinal dt | throw "`tFinal` / `dt` is not a natural number"
    let X0 ← parseZonotopeFixed dops.readExact n (← field req "X0")
    let U ← match fieldOpt req "U" with
      | some j => parseZonotopeFixed dops.readExact e j
      | none => pure (Zonotope.origin e)
    -- the network must run on the initial set (its layers parse and fit)
    match networkOnZonotope dops "neurNetContrSys.reach" req n X0 with
    | .error msg => throw msg
    | .ok ⟨k, _⟩ => if k ≠ m then throw s!"the network gives {k} outputs, `m` is {m}"
    let enlarge ← scalarOrDefault dops req "enlarge" 2476979795053773 (-51)
    let fuel ← natOrDefault req "fuel" 10000
    let step ← parseLinearStep req
    -- the state set at the end of every period
    let mut sets : Array Json := #[]
    for i in List.range H do
      let jt := NeurNetContrSys.joint (aux_network dops req n m)
      match fm.reachClosedLoopFloat jt U options N enlarge fuel step X0 (i + 1) with
      | none => throw s!"period {i + 1}: the network or a step failed"
      | some R =>
        if !noNaN (𝕋 := 𝕋) R then throw tanPoisonMsg
        sets := sets.push (printZonotope dops.showExact R)
    pure [("timePoint", Json.arr sets)]
  else throw s!"`f` has {fs.size} components, expected n = {n}"

/-- Every op of `neurNetContrSys.`, without the prefix. -/
def neurNetContrSysOpNames : List String := [ "reach" ]

/-- `op` of `neurNetContrSys.`, run; `none` for a name this file does not serve. -/
@[noinline, nospecialize]
def handleNeurNetContrSysOp (dops : DtypeOps 𝕋) (op : String) (req : Json) : Option Resp :=
  match op with
  | "reach" => some (handleNeurNetContrSysReach dops req)
  | _ => none

end CORALean.Oracle


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
