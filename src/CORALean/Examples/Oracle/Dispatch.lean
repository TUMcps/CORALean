import CORALean.Examples.Oracle.GitInfo
import CORALean.Examples.Oracle.Ops.ClassOps
import CORALean.Examples.Oracle.Ops.Enclosure
import CORALean.Examples.Oracle.Ops.FromRound
import CORALean.Examples.Oracle.Ops.IntervalOps
import CORALean.Examples.Oracle.Ops.Reach
import CORALean.Examples.Oracle.Ops.ZonotopeMethods
import CORALean.Examples.Oracle.Ops.ZonotopeOps
import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

/-!
# One request line to one response `Json`

`respond` is the whole protocol from the transport's point of view: parse the line, run the
request, echo `id` either way. A malformed line, not JSON or JSON missing `op`/`dtype`, becomes
`{"ok":false,"error":...}` the same way an op's own failure does, never a crash; `Oracle.lean`'s
loop calls this once per line and nothing else. `"ping"` is the one op that needs no `dtype`, so it
is checked first; every other op goes through `withDtype`, where a dtype string becomes a type, and
`handleOp`, where an op name becomes a handler.

## Inputs
* none

## Output
* names of the operations the oracle serves
-/

-- Authors:       Claude Opus 5.5
-- Written:       30-September-2026
-- Last update:   30-September-2026
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Oracle

open CORALean CORALean.Float
open Lean (Json)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The ops that predate the class prefixes: served unprefixed as before. `mtimes`, `plus`,
`reduce`, `interval` and `linComb` mean the zonotope's, `mtimesInterval`, `plusBox`, `plusInterval`
and `enclosure` are zonotope-only. -/
def legacyOpNames : List String :=
  [ "ping", "from", "roundTo", "mtimes", "mtimesInterval", "plus", "plusBox", "plusInterval",
    "linComb", "reduce", "interval", "enclosure", "linearSysReach" ]

/-- The legacy zonotope ops, also reachable as `zonotope.<name>` with the same request and
response. -/
def legacyZonotopeNames : List String :=
  [ "mtimes", "mtimesInterval", "plus", "plusBox", "plusInterval", "linComb", "reduce", "interval",
    "enclosure" ]

/-- Every op name, for `ping` and for an unknown-op error: the legacy names and every
`interval.<name>` and `zonotope.<name>`. A name only one class serves also works without its
prefix, `sin` for `interval.sin`, and is not listed. -/
@[noinline]
def opNames : List String :=
  legacyOpNames ++ intervalOpNames.map ("interval." ++ ·) ++
    (zonotopeOpNames ++ legacyZonotopeNames).map ("zonotope." ++ ·) ++ classOpNames

/-- The legacy zonotope op `op`, run; `none` for any other name. -/
def handleLegacyZonotope {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]
    (dops : DtypeOps 𝕋) (op : String) (req : Json) :
    Option (Except String (List (String × Json))) :=
  match op with
  | "mtimes" =>
    if (fieldOpt req "M" >>= (fieldOpt · "inf")).isSome then some (handleMtimesInterval dops req)
    else some (handleMtimes dops req)
  | "mtimesInterval" => some (handleMtimesInterval dops req)
  | "plus" =>
    if (fieldOpt req "I").isSome then some (handlePlusBox dops req) else some (handlePlus dops req)
  | "plusBox" | "plusInterval" => some (handlePlusBox dops req)
  | "linComb" => some (handleLinComb dops req)
  | "reduce" => some (handleReduce dops req)
  | "interval" => some (handleInterval dops req)
  | "enclosure" => some (handleEnclosure dops req)
  | _ => none

/-- `op` at the scalar `dops` names: `interval.<name>` and `zonotope.<name>` go to that class, a
bare name to its legacy handler, else to the one class serving it, and is refused if both do.
A trailing `_` is dropped, `contains_` is `contains`. -/
@[noinline, nospecialize]
def handleOp {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] (dops : DtypeOps 𝕋)
    (opRaw : String)
    (req : Json) : Except String (List (String × Json)) :=
  let op := if opRaw.endsWith "_" then (opRaw.dropEnd 1).copy else opRaw
  let unknown : Except String (List (String × Json)) :=
    throw s!"unknown op `{opRaw}` -- one of {String.intercalate ", " opNames}"
  -- the class prefixes, then the bare names
  match op.splitOn "." with
  | ["interval", name] =>
    (handleIntervalOp dops name req).getD
      ((handleConversionOp dops "interval" name req).getD unknown)
  | ["zonotope", name] =>
    (handleZonotopeOp dops name req).getD ((handleLegacyZonotope dops name req).getD
      ((handleConversionOp dops "zonotope" name req).getD unknown))
  | [cls, name] =>
    match handleClassOp dops cls name req with
    | some r => r
    | none => unknown
  -- a name without a class prefix
  | _ =>
    match op with
    | "from" => handleFrom dops req
    | "roundTo" => handleRoundTo dops req
    | "linearSysReach" => handleLinearSysReach dops req
    | _ =>
      match handleLegacyZonotope dops op req with
      | some r => r
      | none =>
        if intervalOpNames.contains op && zonotopeOpNames.contains op then
          throw s!"op `{op}` exists for both classes -- use `interval.{op}` or `zonotope.{op}`"
        else
          match handleIntervalOp dops op req with
          | some r => r
          | none => (handleZonotopeOp dops op req).getD unknown

/-- The response to `ping`: the version, whether the tree is dirty, the dtypes and the ops served.
-/
@[noinline]
def pingFields (dtypes : DtypeSet) (version : CoraleanVersion) : List (String × Json) :=
  [ ("version", Json.str version.version),
    ("dirty", Json.bool version.dirty),
    ("dtypes", Json.arr (dtypes.forms.toArray.map Json.str)),
    ("ops", Json.arr (opNames.toArray.map Json.str)) ]

/-- `j`'s `op`, at its `dtype` unless it is `"ping"`, which needs none. -/
def handleRequest (dtypes : DtypeSet) (version : CoraleanVersion) (j : Json) :
    Except String (List (String × Json)) := do
  let op ← strField j "op"
  if op = "ping" then pure (pingFields dtypes version) else
    let dtypeStr ← strField j "dtype"
    dtypes.resolve dtypeStr fun {𝕋} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] dops =>
      handleOp dops op j

/-- One request line to one response line's `Json` -- never throws, an invalid line becoming
`{"ok":false, ...}` exactly as a valid request's own failure does. -/
def respond (dtypes : DtypeSet) (version : CoraleanVersion) (line : String) : Json :=
  match Json.parse line with
  | .error e => Json.mkObj [("ok", Json.bool false), ("error", Json.str s!"invalid JSON: {e}")]
  | .ok j =>
    let idFields := match fieldOpt j "id" with
      | some idj => [("id", idj)]
      | none => []
    match handleRequest dtypes version j with
    | .ok fields => Json.mkObj (("ok", Json.bool true) :: fields ++ idFields)
    | .error e => Json.mkObj (("ok", Json.bool false) :: ("error", Json.str e) :: idFields)

end CORALean.Oracle


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
