import CORALean.Examples.Bench.Format

/-!
# `lake exe bench <exp> --type dyadic|float --format binary64 [--config FILE] ...`

The one place the command line is read. `--reps` and `--out` override the
config's own `reps` and the harness's default output directory; everything
else about a run comes from the config file, which is the point of having one.

`--format` is validated here, against `formatToPrec`, so a bad label is
reported once rather than resurfacing wherever `args.format` is read later.
`--prec` is the raw-bit-count escape hatch and is not checked against
anything, `Dyadic` accepting any `p`; `--prec` wins if both are given.
-/

-- Authors:       Tobias Ladner
-- Written:       25-September-2026
-- Last update:   25-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench

/-- One parsed invocation. `outDir` defaults to `experiments/results`, relative
to the current directory -- `lake exe bench` and `lake env lean --run` are both
meant to be run from the repository root, which `experiments/README.md` says. -/
structure CliArgs where
  experiment : String
  ty : String := "dyadic"
  format : Option String := none
  prec : Option Nat := none
  config : String := "experiments/config/headline_default.json"
  reps : Option Nat := none
  outDir : String := "experiments/results"
  exact : Bool := false


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Parses `args` into a `CliArgs`, defaulting every flag but the experiment
name, which is positional and first. Each flag pattern binds its value
directly, `"--type" :: v :: rest`, so the recursion stays visibly structural. -/
def parseArgs : List String → Except String CliArgs
  | [] => throw "usage: bench <experiment> [--type dyadic|float] \
      [--format binary64|binary32|binary16|binary8|binary4] [--prec P] \
      [--config FILE] [--reps N] [--out DIR] [--exact]"
  | exp :: rest => go rest { experiment := exp }
where
  go : List String → CliArgs → Except String CliArgs
    | [], a => pure a
    | "--type" :: v :: rest, a => do
      if v ≠ "dyadic" ∧ v ≠ "float" then throw s!"`--type` is `dyadic` or `float`, not `{v}`"
      go rest { a with ty := v }
    | "--format" :: v :: rest, a => do
      let _ ← formatToPrec v
      go rest { a with format := some v }
    | "--prec" :: v :: rest, a =>
      match v.toNat? with
      | some p => go rest { a with prec := some p }
      | none => throw s!"`--prec` needs a natural number, not `{v}`"
    | "--config" :: v :: rest, a => go rest { a with config := v }
    | "--reps" :: v :: rest, a =>
      match v.toNat? with
      | some n => go rest { a with reps := some n }
      | none => throw s!"`--reps` needs a natural number, not `{v}`"
    | "--out" :: v :: rest, a => go rest { a with outDir := v }
    | "--exact" :: rest, a => go rest { a with exact := true }
    | [flag], _ => throw s!"`{flag}` needs a value"
    | flag :: _, _ => throw s!"unrecognised argument `{flag}`"

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
