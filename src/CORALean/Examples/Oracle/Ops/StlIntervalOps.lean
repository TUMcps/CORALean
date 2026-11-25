import CORALean.Examples.Oracle.Ops.SetCodec
import CORALean.Examples.Oracle.Ops.StlCodec
import CORALean.Global.Float.DecidableToReal
import CORALean.Specification.STLInterval.Instances
import CORALean.Specification.STLInterval.Operations.And
import CORALean.Specification.STLInterval.Operations.Basic
import CORALean.Specification.STLInterval.Operations.ContainsFloat
import CORALean.Specification.STLInterval.Operations.Infimum
import CORALean.Specification.STLInterval.Operations.Interval
import CORALean.Specification.STLInterval.Operations.IsequalFloat
import CORALean.Specification.STLInterval.Operations.MinkDiff
import CORALean.Specification.STLInterval.Operations.Minus
import CORALean.Specification.STLInterval.Operations.MinusInterval
import CORALean.Specification.STLInterval.Operations.MinusNum
import CORALean.Specification.STLInterval.Operations.Plus
import CORALean.Specification.STLInterval.Operations.PlusInterval
import CORALean.Specification.STLInterval.Operations.PlusNum
import CORALean.Specification.STLInterval.Operations.RepresentsaFloat
import CORALean.Specification.STLInterval.Operations.Supremum
import CORALean.Specification.STLInterval.Operations.ToLeft
import CORALean.Specification.STLInterval.Operations.ToRight
import CORALean.Specification.STLInterval.Operations.WithinTolFloat

/-!
# The STL interval ops: CORA's stlInterval, its set operations and its comparisons

`stlInterval.<name>` runs CORALean's float definition of CORA's `@stlInterval/<name>.m`
(Specification/STLInterval/Operations/), the intervals in `StlCodec`'s format. The bounds of
a sum or difference are rounded outward, which is the nearest rounding at `nearest`. A bound of
`infimum`/`supremum` is a scalar, `"inf"`, or `"nan"` for the empty interval (CORA's NaN).
`contains` of a number decides CORALean's `containsPoint` exactly on the stored bounds.

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

/-- An end of `infimum`/`supremum`: the bound (`"nan"` for the empty interval) and whether it is
attained. -/
private def aux_printEndpoint (dops : DtypeOps 𝕋) (e : STLInterval.Endpoint 𝕋) : Resp :=
  pure [("value", match e.value with
      | none => Json.str "nan"
      | some u => printUpperBound dops u), ("closed", Json.bool e.closed)]

/-- The one-dimensional box `K` of the request, `{"inf","sup"}` of one row. -/
private def aux_parseBox1 (dops : DtypeOps 𝕋) (j : Json) :
    Except String (Real.Interval (Vec 𝕋 1)) := do
  let b ← parseBox dops.readExact j
  if h : b.n = 1 then
    pure ⟨fun _ => b.I.inf ⟨0, by omega⟩, fun _ => b.I.sup ⟨0, by omega⟩⟩
  else throw s!"the box `K` must be one-dimensional, not {b.n}-dimensional"

/-- Whether it is the empty interval (CORA's isemptyobject). -/
private def aux_isEmpty : STLInterval 𝕋 → Bool
  | .empty => true
  | .nonempty .. => false

/-- The tolerance `tol` of the request, `0` when it is absent. -/
private def aux_tol (dops : DtypeOps 𝕋) (req : Json) : Except String 𝕋 :=
  match fieldOpt req "tol" with
  | none => pure zero
  | some _ => do dops.readExact "tol" (← scalarField req "tol")

/-- `contains_(I, t, tol)` of a number, decided exactly on the bounds: inside the open interval,
or within the tolerance of a closed end (`STLInterval.containsPoint`). -/
private def aux_containsPoint (tol : 𝕋) : STLInterval 𝕋 → 𝕋 → Bool
  | .empty, _ => false
  | .nonempty l u lc rc _ _ _, t =>
    -- strictly inside, then at one of the closed ends
    let inside := !(ExactLe.le t l) && (match u with
      | some u => !(ExactLe.le u t)
      | none => true)
    inside || (lc && ExactLe.withinTol tol l t) ||
      (rc && STLInterval.withinTolFloat tol u (some t))

/-- The other operand of `plus`/`minus`: an interval `J`, a number `c` or a box `K`. -/
private inductive aux_Operand (𝕋 : Type) [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]
  | interval (J : STLInterval 𝕋)
  | num (c : 𝕋)
  | box (K : Real.Interval (Vec 𝕋 1))

/-- The operand of `plus`/`minus`, exactly one of `J`, `c`, `K`. -/
private def aux_operand (dops : DtypeOps 𝕋) (op : String) (req : Json) :
    Except String (aux_Operand 𝕋) :=
  match fieldOpt req "J", fieldOpt req "c", fieldOpt req "K" with
  | some j, none, none => .interval <$> parseStlInterval dops j
  | none, some _, none => do pure (.num (← dops.readExact "c" (← scalarField req "c")))
  | none, none, some k => .box <$> aux_parseBox1 dops k
  | _, _, _ => throw s!"{op}: needs exactly one of `J` (an interval), `c` (a number), `K` (a box)"

/-- `plus(I, c)`: CORA's constructor refuses a negative lower bound. -/
private def aux_plusNum (I : STLInterval 𝕋) (c : 𝕋) : Except String (STLInterval 𝕋) :=
  if hc : toReal (0 : 𝕋) ≤ toReal (addDown I.lowerBound c) then
    pure (I.plusNum c (fun _ => by rwa [toReal_zero_eq] at hc))
  else if aux_isEmpty I then pure .empty
  else throw "plus: the lower bound must stay non-negative (CORA:wrongInputInConstructor)"

/-- `plus(I, K)` of a box: as `aux_plusNum`, the box's infimum moving the lower bound. -/
private def aux_plusBox (I : STLInterval 𝕋) (K : Real.Interval (Vec 𝕋 1)) :
    Except String (STLInterval 𝕋) :=
  if hc : toReal (0 : 𝕋) ≤ toReal (addDown I.lowerBound (K.inf 0)) then
    pure (I.plusInterval K (fun _ _ => by rwa [toReal_zero_eq] at hc))
  else if aux_isEmpty I || !(ExactLe.le (K.inf 0) (K.sup 0)) then pure .empty
  else throw "plus: the lower bound must stay non-negative (CORA:wrongInputInConstructor)"


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `op` of `stlInterval.`, run; `none` for a name this file does not serve. -/
@[noinline, nospecialize]
def handleStlIntervalOp (dops : DtypeOps 𝕋) (op : String) (req : Json) : Option Resp :=
  let I? : Except String (STLInterval 𝕋) := do parseStlInterval dops (← field req "I")
  let reply (J : STLInterval 𝕋) : Resp := pure [("I", printStlInterval dops J)]
  match op with
  -- the constructors and the queries of one interval
  | "stlInterval" => some (do
    checkFields op req ["lb", "ub", "lc", "rc"]
    reply (← parseStlInterval dops req))
  | "empty" => some (do
    checkFields op req ["n"]
    let n ← natField req "n"
    if n ≠ 1 then throw s!"{op}: STL intervals are one-dimensional, not {n}-dimensional"
    reply .empty)
  | "isemptyobject" => some (do
    checkFields op req ["I"]
    valueBool (aux_isEmpty (← I?)))
  | "dim" => some (do
    checkFields op req ["I"]
    pure [("value", Lean.toJson (← I?).dim)])
  -- the ends, the box of the bounds and the closures
  | "infimum" => some (do checkFields op req ["I"]; aux_printEndpoint dops (← I?).infimum)
  | "supremum" => some (do checkFields op req ["I"]; aux_printEndpoint dops (← I?).supremum)
  | "interval" => some (do
    checkFields op req ["I"]
    let K := (← I?).interval
    pure [("K", printIntervalVec dops.showExact (⟨K.inf, K.sup⟩ : Interval (Vec 𝕋 1)))])
  | "leftClosure" => some (do checkFields op req ["I"]; reply (← I?).leftClosure)
  | "rightClosure" => some (do checkFields op req ["I"]; reply (← I?).rightClosure)
  -- the half-lines left and right of an interval; none for the empty one (CORA:emptySet)
  | "toLeft" | "toRight" => some (do
    checkFields op req ["I"]
    let I ← I?
    match (if op = "toLeft" then I.toLeft else I.toRight) with
    | some J => reply J
    | none => throw s!"{op}: the interval is empty (CORA:emptySet)")
  -- the operations of two intervals, or of an interval and a number or a box
  | "and" => some (do
    checkFields op req ["I", "J"]
    reply ((← I?).and_ (← parseStlInterval dops (← field req "J"))))
  | "plus" => some (do
    checkFields op req ["I", "J", "c", "K"]
    match ← aux_operand dops op req with
    | .interval J => reply ((← I?).plus J)
    | .num c => reply (← aux_plusNum (← I?) c)
    | .box K => reply (← aux_plusBox (← I?) K))
  -- the differences, the lower bound clamped at 0
  | "minus" => some (do
    checkFields op req ["I", "J", "c", "K"]
    match ← aux_operand dops op req with
    | .interval J => reply ((← I?).minus J)
    | .num c => reply ((← I?).minusNum c)
    | .box K => reply ((← I?).minusInterval K))
  | "minkDiff" => some (do
    checkFields op req ["I", "J", "type"]
    let type ← match fieldOpt req "type" with
      | none => pure "exact"
      | some _ => strField req "type"
    if type ≠ "exact" ∧ type ≠ "inner" then throw s!"{op}: `type` is exact or inner"
    reply ((← I?).minkDiff (← parseStlInterval dops (← field req "J"))))
  -- the comparisons, the bounds compared up to `tol` (0 when absent)
  | "contains" => some (do
    checkFields op req ["I", "J", "t", "tol"]
    let tol ← aux_tol dops req
    match fieldOpt req "J", fieldOpt req "t" with
    | some j, none => valueBool ((← I?).containsFloat tol (← parseStlInterval dops j))
    | none, some _ =>
      valueBool (aux_containsPoint tol (← I?) (← dops.readExact "t" (← scalarField req "t")))
    | _, _ => throw s!"{op}: needs exactly one of `J` (an interval) and `t` (a number)")
  -- equal bounds and ends, and the set types
  | "isequal" => some (do
    checkFields op req ["I", "J", "tol"]
    let J ← parseStlInterval dops (← field req "J")
    valueBool ((← I?).isequalFloat (← aux_tol dops req) J))
  | "representsa" => some (do
    checkFields op req ["I", "type", "tol"]
    let type ← match ← strField req "type" with
      | "emptySet" => pure STLInterval.RepresentsaType.emptySet
      | "stlInterval" => pure .stlInterval
      | "point" => pure .point
      | "origin" => pure .origin
      | t => throw s!"{op}: `type` is emptySet, stlInterval, point or origin, not `{t}`"
    valueBool ((← I?).representsaFloat (← aux_tol dops req) type))
  | _ => none

/-- Every op of `stlInterval.`, without the prefix. -/
def stlIntervalOpNames : List String :=
  [ "stlInterval", "empty", "isemptyobject", "dim", "infimum", "supremum", "interval",
    "leftClosure", "rightClosure", "toLeft", "toRight", "and", "plus", "minus", "minkDiff",
    "contains", "isequal", "representsa" ]

end CORALean.Oracle


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
