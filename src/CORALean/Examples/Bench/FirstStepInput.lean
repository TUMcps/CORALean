import Lean.Data.Json

/-!
# `firststep`: reading `--in FILE`

`experiments/firststep/configs.json` names the system config (`base_config`, a path in the
shape of `experiments/config/*.json`), the step sizes `dts` (rational strings), and `runs`: one
number type each, as `--type`/`--format`/`--prec`/`--digits` name it on the command line. Every
run is taken at every `dt`.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench

open Lean (Json)

/-- One number type: `ty` is `dyadic`, `flint`, `ieee`, `fixed` or `nearest`; `format` is a
`Format.lean` label, `prec` a raw significand width and `digits` a fixed-point digit count. -/
structure FirstStepRun where
  ty : String
  format : Option String
  prec : Option Nat
  digits : Option Nat
deriving Repr

/-- The whole input file. -/
structure FirstStepInput where
  baseConfig : String
  dts : Array String
  runs : Array FirstStepRun
deriving Repr


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

def aux_optStr (j : Json) (k : String) : Option String := (j.getObjVal? k).toOption.bind
  fun v => v.getStr?.toOption

def aux_optNat (j : Json) (k : String) : Option Nat := (j.getObjVal? k).toOption.bind
  fun v => v.getNat?.toOption

def aux_run (j : Json) : Except String FirstStepRun := do
  let ty ← (← j.getObjVal? "type").getStr?
  pure { ty := ty, format := aux_optStr j "format", prec := aux_optNat j "prec",
         digits := aux_optNat j "digits" }


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Reads and parses `path`, wrapping either failure into one `IO` error. Also returns the raw
`Json`, which the output echoes into `meta.input` verbatim. -/
def loadFirstStepInput (path : System.FilePath) : IO (Json × FirstStepInput) := do
  let text ← IO.FS.readFile path
  match Json.parse text with
  | .error e => throw (IO.userError s!"{path}: invalid JSON: {e}")
  | .ok j =>
    let parsed : Except String FirstStepInput := do
      let base ← (← j.getObjVal? "base_config").getStr?
      let dts ← (← (← j.getObjVal? "dts").getArr?).mapM Json.getStr?
      let runs ← (← (← j.getObjVal? "runs").getArr?).mapM aux_run
      pure { baseConfig := base, dts := dts, runs := runs }
    match parsed with
    | .error e => throw (IO.userError s!"{path}: {e}")
    | .ok i => pure (j, i)

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
