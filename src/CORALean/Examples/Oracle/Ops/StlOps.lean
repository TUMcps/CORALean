import CORALean.Examples.Oracle.Ops.SetCodec
import CORALean.Examples.Oracle.Ops.StlCodec
import CORALean.Global.Float.DecidableToReal
import CORALean.Specification.STL.Operations.Basic
import CORALean.Specification.STL.Operations.TreeCombineNextFloat
import CORALean.Specification.STL.Operations.TreeCompare
import CORALean.Specification.STL.Operations.TreeConjunctiveNormalForm
import CORALean.Specification.STL.Operations.TreeDesugar
import CORALean.Specification.STL.Operations.TreeDisjunctiveNormalForm
import CORALean.Specification.STL.Operations.TreeGetVariables
import CORALean.Specification.STL.Operations.TreeIsLinearPredicate
import CORALean.Specification.STL.Operations.TreeTemporal
import CORALean.Specification.STLInterval.Operations.Plus
import CORALean.Specification.STLInterval.Operations.PlusNum

/-!
# The STL ops: CORA's stl formulas, their normal forms, their times and trace checking

`stl.<name>` runs CORALean's definition of CORA's `@stl/<name>.m` on `STL.Tree 𝕋 𝕋 n`
(Specification/STL/Operations/), the formulas in `StlCodec`'s format with `n` variables. Every
reply but `modelCheckTrace` is a structure, served at every dtype; `maximumTime`, `minimumTime`,
`combineNext` and `getTimes` round their sums outward (nearest at `nearest`). `isequal`,
`getTimes` and `modelCheckTrace` have no definition in Specification/STL/ and follow CORA.cpp's
code in its order; `modelCheckTrace` is served at `nearest` only.

## Inputs
* `dops` – dtype operations
* `op` – op name, without the prefix
* `req` – request

## Output
* the op's reply
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

/-- `a < b` and `a == b` as C++ compares doubles. -/
private def aux_lt (a b : 𝕋) : Bool := le a b && !(le b a)
private def aux_eq (a b : 𝕋) : Bool := le a b && le b a

-- (the comparison of CORA's isequal)

/-- CORA's `isequal` of two expressions: sums and products commute, numbers compare by value,
a power also by its exponent (CORA.cpp's `StlExpr::isequal`). -/
private def aux_exprEq {n : Nat} : STL.Expr 𝕋 n → STL.Expr 𝕋 n → Bool
  | .var i, .var j => i == j
  | .num a, .num b => aux_eq a b
  | .pow a k, .pow b l => k == l && aux_exprEq a b
  | .sub a₁ a₂, .sub b₁ b₂ => aux_exprEq a₁ b₁ && aux_exprEq a₂ b₂
  | .add a₁ a₂, .add b₁ b₂ | .mul a₁ a₂, .mul b₁ b₂ =>
    (aux_exprEq a₁ b₁ && aux_exprEq a₂ b₂) || (aux_exprEq a₁ b₂ && aux_exprEq a₂ b₁)
  | _, _ => false

/-- CORA's `isequal` of two formulas: `&` and `|` commute, the windows compare by their bounds
(CORA.cpp's `Stl::isequal`). -/
private def aux_treeEq {n : Nat} : STL.Tree 𝕋 𝕋 n → STL.Tree 𝕋 𝕋 n → Bool
  | .tt, .tt | .ff, .ff => true
  | .cmp c a₁ a₂, .cmp d b₁ b₂ => stlCmpName c == stlCmpName d && aux_exprEq a₁ b₁ &&
      aux_exprEq a₂ b₂
  | .and φ₁ φ₂, .and ψ₁ ψ₂ | .or φ₁ φ₂, .or ψ₁ ψ₂ =>
    (aux_treeEq φ₁ ψ₁ && aux_treeEq φ₂ ψ₂) || (aux_treeEq φ₁ ψ₂ && aux_treeEq φ₂ ψ₁)
  | .not φ, .not ψ => aux_treeEq φ ψ
  -- the temporal operators: the bounds, then the operands
  | .finally a b φ, .finally c d ψ | .globally a b φ, .globally c d ψ =>
    aux_eq a c && aux_eq b d && aux_treeEq φ ψ
  | .next a φ, .next c ψ => aux_eq a c && aux_treeEq φ ψ
  | .until a b φ₁ φ₂, .until c d ψ₁ ψ₂ | .release a b φ₁ φ₂, .release c d ψ₁ ψ₂ =>
    aux_eq a c && aux_eq b d && aux_treeEq φ₁ ψ₁ && aux_treeEq φ₂ ψ₂
  | _, _ => false

-- (the times of the identified parts, getTimes)

/-- The time a part is looked at: a point, or a window once an operator with a window passed. -/
private inductive aux_Time (𝕋 : Type) [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]
  | point (t : 𝕋)
  | window (I : STLInterval 𝕋)

/-- CORA's `stlInterval(a, b)` of a closed window. -/
private def aux_window (a b : 𝕋) : STLInterval 𝕋 :=
  STLInterval.stlIntervalBounds a (some b) true true

/-- The window `I` moved by `c ≥ 0` (CORA's `I + c`); CORA's constructor error below `0`. -/
private def aux_shiftWindow (I : STLInterval 𝕋) (c : 𝕋) : Except String (STLInterval 𝕋) :=
  if hc : toReal (0 : 𝕋) ≤ toReal (addDown I.lowerBound c) then
    pure (I.plusNum c (fun _ => by rwa [toReal_zero_eq] at hc))
  else throw "getTimes: a window below 0 (CORA:wrongInputInConstructor)"

/-- The time under an operator with the window `w`: the window plus the time. -/
private def aux_under (w : STLInterval 𝕋) : aux_Time 𝕋 → Except String (aux_Time 𝕋)
  | .point t => .window <$> aux_shiftWindow w t
  | .window I => pure (.window (w.plus I))

/-- `aux_recursive(obj, time)` of CORA.cpp's `get_times` on the formula `assignIdentifiers`
numbers: each part that is not temporal is the next identifier, and records its time. -/
private def aux_times {n : Nat} : STL.Tree 𝕋 𝕋 n → aux_Time 𝕋 →
    Array (aux_Time 𝕋) → Except String (Array (aux_Time 𝕋))
  -- & and | pass the time to both operands, a temporal ~ to its operand
  | .and φ ψ, time, acc => if φ.temporal || ψ.temporal then do
      aux_times ψ time (← aux_times φ time acc) else pure (acc.push time)
  | .or φ ψ, time, acc => if φ.temporal || ψ.temporal then do
      aux_times ψ time (← aux_times φ time acc) else pure (acc.push time)
  | .not φ, time, acc => if φ.temporal then aux_times φ time acc else pure (acc.push time)
  -- next shifts the time, a point as a point and a window as a window
  | .next a φ, .point t, acc => aux_times φ (.point (addUp a t)) acc
  | .next a φ, .window I, acc => do aux_times φ (.window (← aux_shiftWindow I a)) acc
  -- an operator with a window: the window plus the time
  | .until a b φ ψ, time, acc | .release a b φ ψ, time, acc => do
    let inner ← aux_under (aux_window a b) time
    aux_times ψ inner (← aux_times φ inner acc)
  | .finally a b φ, time, acc | .globally a b φ, time, acc => do
    aux_times φ (← aux_under (aux_window a b) time) acc
  | _, time, acc => pure (acc.push time)

-- (the trace check, modelCheckTrace)

/-- The value of an expression at a state, in CORA.cpp's `priv_eval` order; an integer power is
the repeated product from `1` (and its reciprocal for a negative exponent). -/
private def aux_eval {n : Nat} (x : Fin n → 𝕋) : STL.Expr 𝕋 n → 𝕋
  | .var i => x i
  | .num c => c
  | .add a b => addUp (aux_eval x a) (aux_eval x b)
  | .sub a b => addUp (aux_eval x a) (neg (aux_eval x b))
  | .mul a b => mulUp (aux_eval x a) (aux_eval x b)
  | .pow a k =>
    let base := aux_eval x a
    let prod := (List.replicate k.natAbs base).foldl mulUp one
    if k < 0 then divUp one prod else prod

/-- `std::abs`, and CORA.cpp's `within_tol(a, b, tol)` in floats. -/
private def aux_abs (a : 𝕋) : 𝕋 := if le zero a then a else neg a
private def aux_withinTol (tol a b : 𝕋) : Bool :=
  let d := aux_abs (addUp a (neg b))
  let small := if aux_lt (aux_abs b) (aux_abs a) then aux_abs b else aux_abs a
  aux_eq a b || le d tol || le d (mulUp tol small)

/-- CORA's `aux_until` in CORA.cpp's order: the samples from which a witness of `rhs` within the
window comes before `lhs` fails; the window slides one sample per start sample. -/
private def aux_until (lhs rhs : Array Bool) (t : Array 𝕋) (a b : 𝕋) : Array Bool := Id.run do
  let m := t.size
  let mut ind : Array Nat :=
    (Array.range m).filter fun i => le a (t.getD i zero) && le (t.getD i zero) b
  let mut res := Array.replicate m false
  for cnt in [0:m] do
    if ind.isEmpty || m ≤ ind[0]! then break
    ind := ind.filter (· < m)
    -- the first failure of lhs from cnt on, the first witness of rhs in the window
    let a1 := (List.range' cnt (ind.back! + 1 - cnt)).find? fun k => !lhs[k]!
    let a2 := ((List.range ind.size).find? fun j => rhs[ind[j]!]!).map (ind[0]! + ·)
    match a2 with
    | some w =>
      if a1.all fun f => w < f && ind[0]! ≤ f + 1 then res := res.set! cnt true
    | none => pure ()
    ind := ind.map (· + 1)
  return res

/-- CORA's `aux_recursive` of `modelCheckTrace`: the values of the formula at every sample. -/
private def aux_check {n : Nat} (tol : 𝕋) (X : Array (Fin n → 𝕋)) (t : Array 𝕋) :
    STL.Tree 𝕋 𝕋 n → Array Bool
  | .tt => Array.replicate X.size true
  | .ff => Array.replicate X.size false
  | .cmp c e₁ e₂ => X.map fun x =>
    let a := aux_eval x e₁
    let b := aux_eval x e₂
    match c with
    | .lt => aux_lt a b
    | .le => le a b
    | .gt => aux_lt b a
    | .ge => le b a
  | .not φ => (aux_check tol X t φ).map (!·)
  | .and φ ψ => (aux_check tol X t φ).zipWith (· && ·) (aux_check tol X t ψ)
  | .or φ ψ => (aux_check tol X t φ).zipWith (· || ·) (aux_check tol X t ψ)
  -- next: the values from the first sample at the shift on, within tolerance
  | .next a φ =>
    let lhs := aux_check tol X t φ
    let at? (i : Nat) := le a (t.getD i zero) || aux_withinTol tol (t.getD i zero) a
    let first := ((List.range t.size).find? at?).getD t.size
    (Array.range t.size).map fun i => i + first < t.size && lhs[i + first]!
  -- finally and globally are until with true on the left
  | .finally a b φ => aux_until (Array.replicate X.size true) (aux_check tol X t φ) t a b
  | .globally a b φ =>
    (aux_until (Array.replicate X.size true) ((aux_check tol X t φ).map (!·)) t a b).map (!·)
  | .until a b φ ψ => aux_until (aux_check tol X t φ) (aux_check tol X t ψ) t a b
  -- release: the dual of until, false from the first sample at the end of the window on
  | .release a b φ ψ =>
    let res := (aux_until ((aux_check tol X t φ).map (!·)) ((aux_check tol X t ψ).map (!·)) t a
      b).map (!·)
    let m := t.size
    let idx := ((List.range m).find? fun i => le b (t.getD i zero)).getD m
    let count := if idx < m then min m (idx + 1) else m
    res.mapIdx fun i v => v && i < m - count


/-- `modelCheckTrace` of the trace: only a uniformly sampled one (CORA.cpp's check, the steps
within `eps` of each other), then the value of the formula at the first sample. -/
private def aux_traceCheck {n : Nat} (op : String) (tol : 𝕋) (rows : Array (Fin n → 𝕋))
    (t : Array 𝕋) (φ : STL.Tree 𝕋 𝕋 n) : Resp := do
  let steps := (Array.range (t.size - 1)).map fun i =>
    addUp (t.getD (i + 1) zero) (neg (t.getD i zero))
  let lo := steps.foldl (fun a s => if aux_lt s a then s else a) (steps.getD 0 zero)
  let hi := steps.foldl (fun a s => if aux_lt a s then s else a) (steps.getD 0 zero)
  -- the machine epsilon 2^-52 of binary64, every dtype's eps of CORA.cpp's check
  let eps := (List.replicate 52 ()).foldl (fun e _ => half e) (one : 𝕋)
  if !(le (aux_abs (addUp lo (neg hi))) eps) then
    throw s!"{op}: only uniformly sampled traces are supported (CORA:notSupported)"
  valueBool ((aux_check tol rows t φ).getD 0 false)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `op` of `stl.`, run; `none` for a name this file does not serve. -/
@[noinline, nospecialize]
def handleStlOp (dops : DtypeOps 𝕋) (op : String) (req : Json) : Option Resp :=
  -- the request's variables, formulas, expressions and window
  let nv : Except String Nat := natField req "n"
  let tree (name : String) : Except String (Σ n : Nat, STL.Tree 𝕋 𝕋 n) := do
    let n ← nv
    pure ⟨n, ← parseStlTree dops n (← field req name)⟩
  let time (name : String) : Except String 𝕋 := do dops.readExact name (← scalarField req name)
  -- the replies: a formula, a list of formulas
  let replyTree {n : Nat} (φ : STL.Tree 𝕋 𝕋 n) : Resp := pure [("phi", printStlTree dops φ)]
  let replyList {n : Nat} (L : List (STL.Tree 𝕋 𝕋 n)) : Resp :=
    pure [("list", Json.arr (L.map (printStlTree dops)).toArray)]
  -- the operations of one formula, of two, and of two expressions
  let unary (f : ∀ {n : Nat}, STL.Tree 𝕋 𝕋 n → STL.Tree 𝕋 𝕋 n) (more : List String := []) :
      Resp := do
    checkFields op req (["n", "phi"] ++ more)
    let ⟨_, φ⟩ ← tree "phi"
    replyTree (f φ)
  let binary (f : ∀ {n : Nat}, STL.Tree 𝕋 𝕋 n → STL.Tree 𝕋 𝕋 n → STL.Tree 𝕋 𝕋 n) : Resp := do
    let ⟨n, φ⟩ ← tree "phi"
    let ψ ← parseStlTree dops n (← field req "psi")
    replyTree (f φ ψ)
  let exprs : Except String (Σ n : Nat, STL.Expr 𝕋 n × STL.Expr 𝕋 n) := do
    let n ← nv
    pure ⟨n, ← parseStlExpr dops n (← field req "e1"), ← parseStlExpr dops n (← field req "e2")⟩
  -- a comparison node, and an arithmetic one
  let compare (c : STL.Cmp) : Resp := do
    checkFields op req ["n", "e1", "e2"]
    let ⟨_, e₁, e₂⟩ ← exprs
    replyTree (STL.Tree.compare (τ := 𝕋) c e₁ e₂)
  let arith (f : ∀ {n : Nat}, STL.Expr 𝕋 n → STL.Expr 𝕋 n → STL.Expr 𝕋 n) : Resp := do
    checkFields op req ["n", "e1", "e2"]
    let ⟨_, e₁, e₂⟩ ← exprs
    pure [("e", printStlExpr dops (f e₁ e₂))]
  match op with
  -- the constructor: true, false, or the variables
  | "stl" => some (do
    checkFields op req ["n", "value"]
    match fieldOpt req "value" with
    | some _ => replyTree (if ← boolFieldOr req "value" true then .tt else .ff : STL.Tree 𝕋 𝕋 0)
    | none =>
      let n ← nv
      pure [("vars", Json.arr (Array.ofFn fun i : Fin n =>
        printStlExpr dops (STL.Expr.var (κ := 𝕋) i)))])
  -- the logic and the temporal operators
  | "not" => some (unary .not)
  | "and" => some (do checkFields op req ["n", "phi", "psi"]; binary .and)
  | "or" => some (do checkFields op req ["n", "phi", "psi"]; binary .or)
  | "implies" => some (do checkFields op req ["n", "phi", "psi"]; binary STL.Tree.implies)
  -- the temporal operators of two formulas, then of one
  | "until" => some (do
    checkFields op req ["n", "phi", "psi", "from", "to"]
    let a ← time "from"
    let b ← time "to"
    binary (.until a b))
  | "release" => some (do
    checkFields op req ["n", "phi", "psi", "from", "to"]
    let a ← time "from"
    let b ← time "to"
    binary (.release a b))
  | "finally" => some (do
    let a ← time "from"
    let b ← time "to"
    unary (.finally a b) ["from", "to"])
  | "globally" => some (do
    let a ← time "from"
    let b ← time "to"
    unary (.globally a b) ["from", "to"])
  | "next" => some (do let a ← time "from"; unary (.next a) ["from"])
  -- the comparisons and the arithmetic of expressions
  | "lt" => some (compare .lt)
  | "le" => some (compare .le)
  | "gt" => some (compare .gt)
  | "ge" => some (compare .ge)
  | "plus" => some (arith STL.Expr.plus)
  | "minus" => some (arith STL.Expr.minus)
  | "times" => some (arith STL.Expr.times)
  | "power" => some (do
    checkFields op req ["n", "e1", "k"]
    let n ← nv
    let e ← parseStlExpr dops n (← field req "e1")
    match (← field req "k").getInt? with
    | .ok k => pure [("e", printStlExpr dops (e.power k))]
    | .error _ => throw s!"{op}: `k` must be an integer (CORA:notSupported)")
  -- the rewritings of a formula
  | "desugar" => some (unary STL.Tree.desugar)
  | "negationNormalForm" => some (unary STL.Tree.negationNormalForm)
  | "eliminateTrueFalse" => some (unary STL.Tree.eliminateTrueFalse)
  | "combineNext" => some (unary STL.Tree.combineNextFloat)
  | "conjunctiveNormalForm" | "disjunctiveNormalForm" => some (do
    checkFields op req ["n", "phi", "nnf"]
    let nnf ← boolFieldOr req "nnf" false
    let ⟨_, φ⟩ ← tree "phi"
    replyTree (if op = "conjunctiveNormalForm" then φ.conjunctiveNormalForm nnf
      else φ.disjunctiveNormalForm nnf))
  -- the parts of a formula
  | "assignIdentifiers" => some (do
    checkFields op req ["n", "phi"]
    let ⟨_, φ⟩ ← tree "phi"
    replyList φ.assignIdentifiers)
  | "getClauses" => some (do
    checkFields op req ["n", "phi", "type"]
    let dnf ← match ← strField req "type" with
      | "cnf" => pure false
      | "dnf" => pure true
      | t => throw s!"{op}: `type` is cnf or dnf, not `{t}` (CORA:wrongValue)"
    let ⟨_, φ⟩ ← tree "phi"
    replyList (φ.getClauses dnf))
  | "getVariables" => some (do
    checkFields op req ["n", "phi"]
    let ⟨n, φ⟩ ← tree "phi"
    let vars := (List.finRange n).filter (· ∈ φ.getVariables)
    pure [("vars", Json.arr (vars.map (Lean.toJson ·.val)).toArray)])
  -- the predicates, the latest and earliest times and CORA's comparison
  | "isPredicate" => some (do
    checkFields op req ["n", "phi"]
    valueBool (← tree "phi").2.isPredicate)
  | "isLinearPredicate" => some (do
    checkFields op req ["n", "phi"]
    valueBool (← tree "phi").2.isLinearPredicate)
  | "maximumTime" => some (do
    checkFields op req ["n", "phi"]
    pure [("value", Json.str (dops.showExact (← tree "phi").2.maximumTimeFloat))])
  | "minimumTime" => some (do
    checkFields op req ["n", "phi"]
    pure [("value", Json.str (dops.showExact (← tree "phi").2.minimumTimeFloat))])
  | "isequal" => some (do
    checkFields op req ["n", "phi", "psi"]
    let ⟨n, φ⟩ ← tree "phi"
    valueBool (aux_treeEq φ (← parseStlTree dops n (← field req "psi"))))
  -- the times of the parts `assignIdentifiers` numbers, one list per identifier
  | "getTimes" => some (do
    checkFields op req ["n", "phi"]
    let ⟨_, φ⟩ ← tree "phi"
    let times ← aux_times φ (.point zero) #[]
    let ints := times.map fun | .window I => Json.arr #[printStlInterval dops I] | _ => Json.arr #[]
    let pts := times.map fun
      | .point t => Json.arr #[Json.str (dops.showExact t)]
      | _ => Json.arr #[]
    pure [("timeInt", Json.arr ints), ("timePoint", Json.arr pts)])
  -- the check of a uniformly sampled trace, at nearest
  | "modelCheckTrace" => some (do
    checkFields op req ["n", "phi", "x", "t", "tol"]
    if dops.guaranteed then
      throw s!"{op}: not served at the guaranteed dtype `{dops.label}`: the comparisons are \
        decisions on rounded values; use dtype `nearest`"
    let ⟨n, φ⟩ ← tree "phi"
    let tol ← time "tol"
    -- the states, one per row, and the times
    let X ← parseMatDyn dops.readExact (← field req "x")
    let T ← parseMatDyn dops.readExact (← field req "t")
    if hX : X.c = n ∧ T.c = 1 ∧ T.r = X.r ∧ 0 < X.r then
      let t : Array 𝕋 := Array.ofFn fun i : Fin T.r => T.M i ⟨0, by omega⟩
      let rows : Array (Fin n → 𝕋) := Array.ofFn fun i : Fin X.r => fun k =>
        X.M i (k.cast hX.1.symm)
      aux_traceCheck op tol rows t φ
    else throw s!"{op}: give x as (m, n) and t as (m, 1), m ≥ 1")
  | _ => none
/-- Every op of `stl.`, without the prefix. -/
def stlOpNames : List String :=
  [ "stl", "not", "and", "or", "implies", "until", "release", "finally", "globally", "next", "lt",
    "le", "gt", "ge", "plus", "minus", "times", "power", "desugar", "negationNormalForm",
    "eliminateTrueFalse", "combineNext", "conjunctiveNormalForm", "disjunctiveNormalForm",
    "assignIdentifiers", "getClauses", "getVariables", "isPredicate", "isLinearPredicate",
    "maximumTime", "minimumTime", "isequal", "getTimes", "modelCheckTrace" ]

end CORALean.Oracle


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
