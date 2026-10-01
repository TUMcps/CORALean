import CORALean.Examples.Bench.Format

/-!
# `lake exe bench <exp> --type dyadic|ieee|float|nearest|fixed --format binary64 [--config FILE]`

The one place the command line is read. `--reps` and `--out` override the
config's own `reps` and the harness's default output directory; everything
else about a run comes from the config file, which is the point of having one.

`--format` is validated here, against `formatToPrec`, once. It names the format
for `--type ieee`, only a significand width for `dyadic`/`nearest`. `--prec` is
the raw-bit-count escape hatch, unchecked, and wins if both are given.
`--digits` is its `--type fixed` counterpart, the decimal digit count
`FixedPoint f` rounds to, likewise unchecked.

`--net` and `--images` are `nn-mnist`'s own: which of the three converted
networks (`experiments/nn/mnist/nets/`) to run, and how many of the 100
converted images to use. Left `none` and defaulted by the experiment itself,
the way `--reps` is, rather than validated here -- neither name means
anything to `dtdemo` or `nn-float32`.
-/

-- Authors:       Tobias Ladner
-- Written:       25-September-2026
-- Last update:   01-October-2026
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
  digits : Option Nat := none
  config : String := "experiments/config/headline_default.json"
  reps : Option Nat := none
  outDir : String := "experiments/results"
  exact : Bool := false
  net : Option String := none
  images : Option Nat := none
  /-- `--in`: `opcompare`'s own input file, `experiments/matlab-ops/inputs.json` if `none`, or
  `firststep`'s, `experiments/firststep/configs.json` -- no other experiment reads it. -/
  inFile : Option String := none


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Parses `args` into a `CliArgs`, defaulting every flag but the experiment
name, which is positional and first. Each flag pattern binds its value
directly, `"--type" :: v :: rest`, so the recursion stays visibly structural. -/
def parseArgs : List String → Except String CliArgs
  | [] => throw "usage: bench <experiment> [--type dyadic|ieee|float|nearest|fixed] \
      [--format binary64|binary32|binary16|binary8|binary4] [--prec P] [--digits F] \
      [--config FILE] [--reps N] [--out DIR] [--exact] [--net small|medium|large] \
      [--images K] [--in FILE]"
  | exp :: rest => go rest { experiment := exp }
where
  go : List String → CliArgs → Except String CliArgs
    | [], a => pure a
    | "--type" :: v :: rest, a => do
      if v ≠ "dyadic" ∧ v ≠ "float" ∧ v ≠ "nearest" ∧ v ≠ "fixed" ∧ v ≠ "ieee" then
        throw s!"`--type` is `dyadic`, `ieee`, `float`, `nearest` or `fixed`, not `{v}`"
      go rest { a with ty := v }
    | "--format" :: v :: rest, a => do
      let _ ← formatToPrec v
      go rest { a with format := some v }
    | "--prec" :: v :: rest, a =>
      match v.toNat? with
      | some p => go rest { a with prec := some p }
      | none => throw s!"`--prec` needs a natural number, not `{v}`"
    | "--digits" :: v :: rest, a =>
      match v.toNat? with
      | some d => go rest { a with digits := some d }
      | none => throw s!"`--digits` needs a natural number, not `{v}`"
    | "--config" :: v :: rest, a => go rest { a with config := v }
    | "--reps" :: v :: rest, a =>
      match v.toNat? with
      | some n => go rest { a with reps := some n }
      | none => throw s!"`--reps` needs a natural number, not `{v}`"
    | "--out" :: v :: rest, a => go rest { a with outDir := v }
    | "--exact" :: rest, a => go rest { a with exact := true }
    | "--net" :: v :: rest, a => go rest { a with net := some v }
    | "--images" :: v :: rest, a =>
      match v.toNat? with
      | some k => go rest { a with images := some k }
      | none => throw s!"`--images` needs a natural number, not `{v}`"
    | "--in" :: v :: rest, a => go rest { a with inFile := some v }
    | [flag], _ => throw s!"`{flag}` needs a value"
    | flag :: _, _ => throw s!"unrecognised argument `{flag}`"

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
