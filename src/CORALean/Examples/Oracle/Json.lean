import Lean.Data.Json.Basic
import Lean.Data.Json.Parser
import Lean.Data.Json.Printer
import Lean.Data.Json.FromToJson

/-!
# Reading a request object, with messages that name the field

`Lean.Json`'s own accessors say only `"object expected"` or `"property not
found: k"`; every helper here instead names both the field and, for a type
mismatch, what was read in its place, since a malformed request is the normal
case for this executable and the message is what a caller debugs from.
-/

-- Authors:       Tobias Ladner
-- Written:       30-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Oracle

open Lean (Json)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `j`'s own one-line description, for a message naming what was found -- not `aux_`-named
since `Codec.lean` reuses it too. -/
def kindOf : Json → String
  | .null => "null"
  | .bool _ => "a boolean"
  | .num _ => "a number"
  | .str _ => "a string"
  | .arr _ => "an array"
  | .obj _ => "an object"

/-- `j`'s field `name`, or an error naming it. -/
def field (j : Json) (name : String) : Except String Json :=
  match j.getObjVal? name with
  | .ok v => pure v
  | .error _ => throw s!"missing field `{name}`"

/-- `j`'s field `name` if present, `none` otherwise -- never an error. -/
def fieldOpt (j : Json) (name : String) : Option Json := (j.getObjVal? name).toOption

/-- `j`'s field `name`, as a string, or an error naming the field and what was there instead. -/
def strField (j : Json) (name : String) : Except String String := do
  let v ← field j name
  match v.getStr? with
  | .ok s => pure s
  | .error _ => throw s!"field `{name}` must be a string, not {kindOf v}"

/-- `j`'s field `name`, as a natural number, or an error naming the field. -/
def natField (j : Json) (name : String) : Except String Nat := do
  let v ← field j name
  match v.getNat? with
  | .ok n => pure n
  | .error _ => throw s!"field `{name}` must be a nonnegative integer, not {kindOf v}"

/-- `j`'s field `name`, as an array, or an error naming the field. -/
def arrField (j : Json) (name : String) : Except String (Array Json) := do
  let v ← field j name
  match v.getArr? with
  | .ok a => pure a
  | .error _ => throw s!"field `{name}` must be an array, not {kindOf v}"

end CORALean.Oracle


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
