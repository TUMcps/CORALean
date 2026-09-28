import CORALean.Examples.Bench.OpCompareCodec
import Lean.Data.Json

/-!
# `opcompare`: reading `inputs.json`

`experiments/matlab-ops/make_inputs.py` writes one flat JSON object, every value a hex bit
pattern array under its own key: `v1e4`/`w1e4` (n = 10^4), `cancel` (n = 2000), and the four
row-major matrices `A100`/`B100`/`A500`/`B500`. `InputHex` keeps every token as read, for
`OpCompareCodec.checkRoundTrip`; `decodeInputs` is the one place a token becomes a `Float`.
-/

-- Authors:       Tobias Ladner
-- Written:       28-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench

open Lean (Json)

/-- Every array of `inputs.json`, still hex strings. -/
structure InputHex where
  v1e4 : Array String
  w1e4 : Array String
  cancel : Array String
  A100 : Array String
  B100 : Array String
  A500 : Array String
  B500 : Array String

/-- The same seven arrays, decoded to `Float`. -/
structure Inputs where
  v1e4 : Array Float
  w1e4 : Array Float
  cancel : Array Float
  A100 : Array Float
  B100 : Array Float
  A500 : Array Float
  B500 : Array Float


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

def aux_hexArr (j : Json) (k : String) : Except String (Array String) := do
  (← (← j.getObjVal? k).getArr?).mapM Json.getStr?


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every hex token `InputHex` holds, all seven arrays concatenated -- what
`OpCompareCodec.checkRoundTrip` runs over. -/
def InputHex.allHex (h : InputHex) : Array String :=
  h.v1e4 ++ h.w1e4 ++ h.cancel ++ h.A100 ++ h.B100 ++ h.A500 ++ h.B500

/-- Parses an already-decoded `Json` value into an `InputHex`, failing with a message naming
the missing or malformed field. -/
def parseInputHex (j : Json) : Except String InputHex := do
  pure
    { v1e4 := ← aux_hexArr j "v1e4", w1e4 := ← aux_hexArr j "w1e4"
      cancel := ← aux_hexArr j "cancel"
      A100 := ← aux_hexArr j "A100", B100 := ← aux_hexArr j "B100"
      A500 := ← aux_hexArr j "A500", B500 := ← aux_hexArr j "B500" }

/-- Every field of `h`, decoded to `Float` -- fails only if a token is not a valid 16-hex-digit
binary64 bit pattern, which `checkRoundTrip` never lets reach a computation silently wrong. -/
def decodeInputs (h : InputHex) : Except String Inputs := do
  pure
    { v1e4 := ← h.v1e4.mapM hexToFloat, w1e4 := ← h.w1e4.mapM hexToFloat
      cancel := ← h.cancel.mapM hexToFloat
      A100 := ← h.A100.mapM hexToFloat, B100 := ← h.B100.mapM hexToFloat
      A500 := ← h.A500.mapM hexToFloat, B500 := ← h.B500.mapM hexToFloat }

/-- Reads and parses `path`, wrapping either failure into one `IO` error. -/
def loadInputHex (path : System.FilePath) : IO InputHex := do
  let text ← IO.FS.readFile path
  match Json.parse text with
  | .error e => throw (IO.userError s!"{path}: invalid JSON: {e}")
  | .ok j => match parseInputHex j with
    | .error e => throw (IO.userError s!"{path}: {e}")
    | .ok h => pure h

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
