import Lean.Data.Json

/-!
# The headline config, read once per run

`experiments/config/*.json` is the single source of truth for the spiral
system, read here with `Lean.Json` and by the MATLAB/CORA scripts with
`jsondecode` -- see `experiments/README.md` for the shared schema. Every real
number stays a `String` at this stage; `Bench/Rollout.lean` is where a field is
turned into `CORALean.Bench.ExactDyadic` and then into the scalar a run was
asked for.
-/

-- Authors:       Claude Opus 5.5
-- Written:       25-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench

open Lean (Json)

/-- One `dyadic <format>` or `float` combination a config asks to be run at.
`format` is a label `Format.formatToPrec` reads (`"binary32"` and so on),
`none` for `float`, whose precision is fixed by the type. -/
structure PrecisionSpec where
  ty : String
  format : Option String
deriving Repr

/-- The config file, fields kept as the strings and numbers the JSON holds --
parsing a rational string is `Rational.parseExact`'s job, not this one's. -/
structure HeadlineConfig where
  a : String
  b : String
  dt : String
  x0Center : Array String
  x0Generators : Array (Array String)
  eta : Nat
  rho : Nat
  steps : Nat
  reps : Nat
  precisions : Array PrecisionSpec
deriving Repr


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

def aux_obj (j : Json) (k : String) : Except String Json := j.getObjVal? k
def aux_str (j : Json) (k : String) : Except String String := do (← aux_obj j k).getStr?
def aux_nat (j : Json) (k : String) : Except String Nat := do (← aux_obj j k).getNat?

def aux_strArr (j : Json) : Except String (Array String) := do
  (← j.getArr?).mapM Json.getStr?

def aux_precisionSpec (j : Json) : Except String PrecisionSpec := do
  let ty ← aux_str j "type"
  if ty = "dyadic" then pure ⟨ty, some (← aux_str j "format")⟩ else pure ⟨ty, none⟩


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Parses one already-decoded `Json` value into a `HeadlineConfig`, failing
with a message naming the missing or malformed field. -/
def parseConfig (j : Json) : Except String HeadlineConfig := do
  let sys ← aux_obj j "system"
  let x0 ← aux_obj j "x0"
  let center ← aux_strArr (← aux_obj x0 "center")
  let genRows ← (← aux_obj x0 "generators").getArr?
  let generators ← genRows.mapM aux_strArr
  let precJ ← (← aux_obj j "precisions").getArr?
  let precisions ← precJ.mapM aux_precisionSpec
  let a ← aux_str sys "a"
  let b ← aux_str sys "b"
  let dt ← aux_str j "dt"
  let eta ← aux_nat j "eta"
  let rho ← aux_nat j "rho"
  let steps ← aux_nat j "steps"
  let reps ← aux_nat j "reps"
  pure
    { a := a, b := b, dt := dt, x0Center := center, x0Generators := generators
      eta := eta, rho := rho, steps := steps, reps := reps, precisions := precisions }

/-- Reads and parses a config file, wrapping either failure into one `IO`
error. Also returns the raw `Json`, which `writeRun` echoes into `meta.config`
verbatim rather than re-serialising `HeadlineConfig` and risking drift. -/
def loadConfig (path : System.FilePath) : IO (Json × HeadlineConfig) := do
  let text ← IO.FS.readFile path
  match Json.parse text with
  | .error e => throw (IO.userError s!"{path}: invalid JSON: {e}")
  | .ok j => match parseConfig j with
    | .error e => throw (IO.userError s!"{path}: {e}")
    | .ok cfg => pure (j, cfg)

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
