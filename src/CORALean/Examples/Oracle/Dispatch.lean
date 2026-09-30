import CORALean.Examples.Oracle.GitInfo
import CORALean.Examples.Oracle.Ops.Enclosure
import CORALean.Examples.Oracle.Ops.FromRound
import CORALean.Examples.Oracle.Ops.Reach
import CORALean.Examples.Oracle.Ops.ZonotopeOps

/-!
# One request line to one response `Json`

`respond` is the whole protocol from the transport's point of view: parse the
line, run the request, echo `id` either way. A malformed line -- not JSON, or
JSON missing `op`/`dtype` -- becomes `{"ok":false,"error":...}` the same way an
op's own failure does, never a crash; `Oracle.lean`'s loop calls this once per
line and nothing else.

`"ping"` is the one op that needs no `dtype`, so it is checked first;
every other op goes through `withDtype`, which is where a dtype string becomes
a type, and `handleOp`, which is where an op name becomes a handler.
-/

-- Authors:       Tobias Ladner
-- Written:       30-September-2026
-- Last update:   30-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Oracle

open CORALean CORALean.Float
open Lean (Json)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every op name, for `ping` and for an unknown-op error. -/
def opNames : List String :=
  [ "ping", "from", "roundTo", "mtimes", "mtimesInterval", "plus", "plusBox", "plusInterval",
    "linComb", "reduce", "interval", "enclosure", "linearSysReach" ]

/-- `op`, run at the scalar `dops` names. -/
def handleOp {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] (dops : DtypeOps 𝕋) (op : String)
    (req : Json) : Except String (List (String × Json)) :=
  match op with
  | "from" => handleFrom dops req
  | "roundTo" => handleRoundTo dops req
  | "mtimes" => handleMtimes dops req
  | "mtimesInterval" => handleMtimesInterval dops req
  | "plus" => handlePlus dops req
  | "plusBox" | "plusInterval" => handlePlusBox dops req
  | "linComb" => handleLinComb dops req
  | "reduce" => handleReduce dops req
  | "interval" => handleInterval dops req
  | "enclosure" => handleEnclosure dops req
  | "linearSysReach" => handleLinearSysReach dops req
  | o => throw s!"unknown op `{o}` -- one of {String.intercalate ", " opNames}"

def pingFields (version : CoraleanVersion) : List (String × Json) :=
  [ ("version", Json.str version.version),
    ("dirty", Json.bool version.dirty),
    ("dtypes", Json.arr (dtypeForms.toArray.map Json.str)),
    ("ops", Json.arr (opNames.toArray.map Json.str)) ]

/-- `j`'s `op`, at its `dtype` unless it is `"ping"`, which needs none. -/
def handleRequest (version : CoraleanVersion) (j : Json) :
    Except String (List (String × Json)) := do
  let op ← strField j "op"
  if op = "ping" then pure (pingFields version) else
    let dtypeStr ← strField j "dtype"
    withDtype dtypeStr fun {𝕋} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] dops =>
      handleOp dops op j

/-- One request line to one response line's `Json` -- never throws, an invalid line becoming
`{"ok":false, ...}` exactly as a valid request's own failure does. -/
def respond (version : CoraleanVersion) (line : String) : Json :=
  match Json.parse line with
  | .error e => Json.mkObj [("ok", Json.bool false), ("error", Json.str s!"invalid JSON: {e}")]
  | .ok j =>
    let idFields := match fieldOpt j "id" with
      | some idj => [("id", idj)]
      | none => []
    match handleRequest version j with
    | .ok fields => Json.mkObj (("ok", Json.bool true) :: fields ++ idFields)
    | .error e => Json.mkObj (("ok", Json.bool false) :: ("error", Json.str e) :: idFields)

end CORALean.Oracle


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
