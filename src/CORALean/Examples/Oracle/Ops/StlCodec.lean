import CORALean.Examples.Oracle.Ops.OpCommon
import CORALean.Examples.Oracle.Codec
import CORALean.Global.Float.ExactLe
import CORALean.Specification.STL.Definitions.Tree
import CORALean.Specification.STLInterval.Operations.StlIntervalBounds

/-!
# The wire format of STL formulas and STL intervals

An expression is `{"x":i}` (0-based, CORA's `x<i+1>`), `{"const":s}`, `{"op":"add"|"sub"|"mul",
"args":[a,b]}` or `{"op":"pow","args":[a],"exponent":k}`. A formula is `{"op":op,"args":[...]}`
with `op` one of `true`, `false`, `<`, `<=`, `>`, `>=` (two expressions), `not`, `and`, `or`,
`until`, `release` (with `from`, `to`), `finally`, `globally` (with `from`, `to`) and `next` (with
`from`); the windows are closed. An interval is `{"lb","ub","lc","rc"}`, `ub` the string `"inf"`
when unbounded, or `{"empty":true}`.

## Inputs
* `dops` – dtype operations
* `n` – the number of variables
* `j` – the JSON object

## Output
* the formula, the expression or the interval, or an error naming the field
-/

-- Authors:       Claude Opus 5.5
-- Written:       25-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Oracle

open CORALean CORALean.Float FloatOps SoundFloatArithmetic
open Lean (Json)

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A comparison by CORA's name. -/
private def aux_cmpOf : String → Option STL.Cmp
  | "<" => some .lt
  | "<=" => some .le
  | ">" => some .gt
  | ">=" => some .ge
  | _ => none

/-- A node of a reply: its name, its operands, and further fields. -/
private def aux_node (op : String) (args : List Json) (more : List (String × Json) := []) :
    Json :=
  Json.mkObj ([("op", Json.str op)] ++ more ++ [("args", Json.arr args.toArray)])


-- =====================================  MAIN DEFINITION  ====================================== --

/-- An expression of the request (see the module docstring). -/
partial def parseStlExpr (dops : DtypeOps 𝕋) (n : Nat) (j : Json) :
    Except String (STL.Expr 𝕋 n) := do
  match fieldOpt j "x", fieldOpt j "const" with
  | some _, _ =>
    let i ← natField j "x"
    if h : i < n then pure (.var ⟨i, h⟩) else throw s!"variable x_{i} with only {n} variables"
  | _, some _ => pure (.num (← dops.readExact "const" (← scalarField j "const")))
  | none, none =>
    let op ← strField j "op"
    let args ← (← arrField j "args").mapM (parseStlExpr dops n)
    -- the sums, differences and products, then the integer powers
    match op, args.toList with
    | "add", [a, b] => pure (.add a b)
    | "sub", [a, b] => pure (.sub a b)
    | "mul", [a, b] => pure (.mul a b)
    | "pow", [a] =>
      match (← field j "exponent").getInt? with
      | .ok k => pure (.pow a k)
      | .error _ => throw "pow: `exponent` must be an integer"
    | _, _ => throw s!"unknown expression `{op}` or wrong number of arguments"

/-- An expression of a reply. -/
def printStlExpr (dops : DtypeOps 𝕋) {n : Nat} : STL.Expr 𝕋 n → Json
  | .var i => Json.mkObj [("x", Lean.toJson i.val)]
  | .num c => Json.mkObj [("const", Json.str (dops.showExact c))]
  | .add a b => aux_node "add" [printStlExpr dops a, printStlExpr dops b]
  | .sub a b => aux_node "sub" [printStlExpr dops a, printStlExpr dops b]
  | .mul a b => aux_node "mul" [printStlExpr dops a, printStlExpr dops b]
  | .pow a k => aux_node "pow" [printStlExpr dops a] [("exponent", Lean.toJson k)]

/-- CORA's name of a comparison. -/
def stlCmpName : STL.Cmp → String
  | .lt => "<"
  | .le => "<="
  | .gt => ">"
  | .ge => ">="

/-- A formula of the request (see the module docstring). -/
partial def parseStlTree (dops : DtypeOps 𝕋) (n : Nat) (j : Json) :
    Except String (STL.Tree 𝕋 𝕋 n) := do
  let op ← strField j "op"
  let args : Array Json := ((fieldOpt j "args").bind (·.getArr?.toOption)).getD #[]
  let time (name : String) : Except String 𝕋 := do dops.readExact name (← scalarField j name)
  -- the constants and the comparisons of expressions
  if op = "true" then return .tt
  if op = "false" then return .ff
  if let some c := aux_cmpOf op then
    match ← args.toList.mapM (parseStlExpr dops n) with
    | [a, b] => return .cmp c a b
    | _ => throw s!"`{op}` compares two expressions"
  -- the operators of formulas
  match op, ← args.toList.mapM (parseStlTree dops n) with
  | "not", [φ] => pure (.not φ)
  | "and", [φ, ψ] => pure (.and φ ψ)
  | "or", [φ, ψ] => pure (.or φ ψ)
  | "until", [φ, ψ] => pure (.until (← time "from") (← time "to") φ ψ)
  | "release", [φ, ψ] => pure (.release (← time "from") (← time "to") φ ψ)
  | "finally", [φ] => pure (.finally (← time "from") (← time "to") φ)
  | "globally", [φ] => pure (.globally (← time "from") (← time "to") φ)
  | "next", [φ] => pure (.next (← time "from") φ)
  | _, _ => throw s!"unknown formula `{op}` or wrong number of operands"

/-- A formula of a reply. -/
def printStlTree (dops : DtypeOps 𝕋) {n : Nat} : STL.Tree 𝕋 𝕋 n → Json
  | .tt => aux_node "true" []
  | .ff => aux_node "false" []
  | .cmp c a b => aux_node (stlCmpName c) [printStlExpr dops a, printStlExpr dops b]
  | .not φ => aux_node "not" [printStlTree dops φ]
  | .and φ ψ => aux_node "and" [printStlTree dops φ, printStlTree dops ψ]
  | .or φ ψ => aux_node "or" [printStlTree dops φ, printStlTree dops ψ]
  -- the temporal operators carry their windows
  | .until a b φ ψ => aux_node "until" [printStlTree dops φ, printStlTree dops ψ]
      [("from", Json.str (dops.showExact a)), ("to", Json.str (dops.showExact b))]
  | .release a b φ ψ => aux_node "release" [printStlTree dops φ, printStlTree dops ψ]
      [("from", Json.str (dops.showExact a)), ("to", Json.str (dops.showExact b))]
  | .finally a b φ => aux_node "finally" [printStlTree dops φ]
      [("from", Json.str (dops.showExact a)), ("to", Json.str (dops.showExact b))]
  | .globally a b φ => aux_node "globally" [printStlTree dops φ]
      [("from", Json.str (dops.showExact a)), ("to", Json.str (dops.showExact b))]
  | .next a φ => aux_node "next" [printStlTree dops φ] [("from", Json.str (dops.showExact a))]

/-- The Boolean field `name` of `j`, `dflt` when it is absent. -/
def boolFieldOr (j : Json) (name : String) (dflt : Bool) : Except String Bool :=
  match fieldOpt j name with
  | none => pure dflt
  | some v => match v.getBool? with
    | .ok b => pure b
    | .error _ => throw s!"field `{name}` must be true or false"

/-- An upper bound: a scalar, or the string `"inf"` for none. -/
def parseUpperBound (dops : DtypeOps 𝕋) (j : Json) (name : String) :
    Except String (WithTop 𝕋) := do
  if (← field j name) == Json.str "inf" then pure ⊤
  else pure (some (← dops.readExact name (← scalarField j name)))

/-- A bound printed: the scalar, or `"inf"`. -/
def printUpperBound (dops : DtypeOps 𝕋) : WithTop 𝕋 → Json
  | some x => Json.str (dops.showExact x)
  | none => Json.str "inf"

/-- An interval of the request, built by CORA's constructor: `{"empty":true}`, or the bounds and
ends; a negative lower bound is CORA's constructor error. -/
def parseStlInterval (dops : DtypeOps 𝕋) (j : Json) : Except String (STLInterval 𝕋) := do
  if (fieldOpt j "empty").isSome then return .empty
  let lb ← dops.readExact "lb" (← scalarField j "lb")
  let ub ← parseUpperBound dops j "ub"
  let lc ← boolFieldOr j "lc" true
  let rc ← boolFieldOr j "rc" true
  if !(ExactLe.le (zero : 𝕋) lb) then
    throw "stlInterval: the lower bound must be non-negative (CORA:wrongInputInConstructor)"
  pure (STLInterval.stlIntervalBounds lb ub lc rc)

/-- An interval of a reply. -/
def printStlInterval (dops : DtypeOps 𝕋) : STLInterval 𝕋 → Json
  | .empty => Json.mkObj [("empty", Json.bool true)]
  | .nonempty l u lc rc _ _ _ => Json.mkObj [("lb", Json.str (dops.showExact l)),
      ("ub", printUpperBound dops u), ("lc", Json.bool lc), ("rc", Json.bool rc)]

end CORALean.Oracle


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
