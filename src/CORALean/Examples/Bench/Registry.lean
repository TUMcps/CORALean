import CORALean.Examples.Bench.Cli
import CORALean.Examples.Bench.Nn
import CORALean.Examples.Bench.Output
import CORALean.Global.Float.Instances.Binary64.API
import CORALean.Global.Float.Instances.Dyadic.API

/-!
# `dtdemo`, and where `headline-a`/`headline-b`/`exp2-timepoint` plug in

`dispatch` is the one place `main` calls into; every experiment name it knows
goes through `runAt`, generic in the scalar `𝕋`, instantiated once at
`Dyadic p` and once at `Float` by `dispatch` itself. `dtdemo` is the only
experiment that runs today -- `LinearSysDT.reach` on the config's spiral,
discretized by `Rollout.buildSystem`'s placeholder Euler step. The other three
are registered and documented so wiring in the verified algorithm later is a
few lines: replace `stub` with a call shaped like `Rollout.rollout`'s, an
`Array (Zonotope 𝕋 2)` (or, for `headline-b`, the time-point array besides the
time-interval one) built from the config's `A`, `X0`, `dt`, `eta`, `rho` and
`steps`.

A `dyadic` run's significand width, `resolvedPrec`, is `--prec` if given (a
raw bit count, for a precision none of the five `--format` labels name), else
`--format` mapped through `formatToPrec` (already validated by `parseArgs`),
else `53` -- `binary64`, so the default agrees with native `Float`.
-/

-- Authors:       Tobias Ladner
-- Written:       25-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench

open CORALean CORALean.Float
open Lean (Json)

/-- `<outDir>/<config name>/<experiment>/<type>[-<format>]`, before the
`.json`/`.csv` extension, so two configs or experiments never collide. -/
def outPath (outDir configPath experiment ty format : String) : System.FilePath :=
  let configName := (System.FilePath.mk configPath).fileStem.getD configPath
  let label := if ty = "float" then ty else s!"{ty}-{format}"
  System.FilePath.mk outDir / configName / experiment / label

/-- Loads the config, builds the system, times and runs `rollout`, and writes
the result -- everything `dtdemo` needs at whichever scalar `dispatch` picked. -/
def runDtdemo {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] (args : CliArgs)
    (inst : String → ExactDyadic → Except String 𝕋) (instUnchecked : ExactDyadic → 𝕋)
    (toD : 𝕋 → Float) (format : String) (toExact : Option (𝕋 → String)) (sig : ℕ) :
    IO Unit := do
  let (configJ, cfg) ← loadConfig args.config
  let S ← match buildSystem cfg inst instUnchecked with
    | .ok S => pure S
    | .error e => throw (IO.userError s!"{args.config}: {e}")
  let dtFloat ← match ExactDyadic.toFloat "dt" (← IO.ofExcept (parseExact cfg.dt)) with
    | .ok v => pure v
    | .error e => throw (IO.userError e)
  let reps := args.reps.getD cfg.reps
  let (samples, medianNs, _checksum, steps) ← timeRollout toD S cfg.rho cfg.steps reps
  let out := outPath args.outDir args.config "dtdemo" args.ty format
  writeRun out "dtdemo" "reach" args.ty format sig configJ cfg.eta samples medianNs toD
    toExact dtFloat steps
  IO.println s!"dtdemo: wrote {out}.json and {out}.csv ({steps.size} steps, median \
    {medianNs} ns over {reps} rep(s))"

/-- Prints where the verified algorithm goes and exits nonzero -- registered,
not implemented yet, per the harness's brief. -/
def stub (name signature : String) : IO Unit := do
  IO.eprintln s!"{name}: not yet available -- plug in `{signature}` in \
    `CORALean.Bench.Registry.dispatch`"
  IO.Process.exit 2


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `args.experiment`, run at whichever `𝕋` `dispatch` picked. The single
obvious place a landed `headline-a`/`headline-b`/`exp2-timepoint` replaces
its `stub` line with a real call. -/
def aux_runAt {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] (args : CliArgs)
    (inst : String → ExactDyadic → Except String 𝕋) (instUnchecked : ExactDyadic → 𝕋)
    (toD : 𝕋 → Float) (format : String) (toExact : Option (𝕋 → String)) (sig : ℕ) :
    IO Unit :=
  match args.experiment with
  | "nn-float32" => runNnFloat32 args
  | "dtdemo" => runDtdemo args inst instUnchecked toD format toExact sig
  | "headline-a" => stub "headline-a" "(A X0 dt eta rho N : _) → Array (Zonotope 𝕋 2)"
  | "headline-b" => stub "headline-b" "(A X0 dt eta rho N : _) → Array (Zonotope 𝕋 2)"
  | "exp2-timepoint" => stub "exp2-timepoint"
      "(A X0 dt eta rho N : _) → Array (Zonotope 𝕋 2) × Array (Zonotope 𝕋 2)"
  | other => do
    IO.eprintln s!"unknown experiment `{other}` -- one of dtdemo, headline-a, \
      headline-b, exp2-timepoint"
    IO.Process.exit 1


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The significand width a `dyadic` run picks: `--prec` if given, else
`--format` (already validated), else `53` -- `binary64`. -/
def resolvedPrec (args : CliArgs) : ℕ :=
  match args.prec with
  | some p => p
  | none => match args.format with
    | some fmt => (formatToPrec fmt).toOption.getD 53
    | none => 53

/-- Runs `args.experiment` at the scalar `args.ty` names -- `Dyadic p` (`p`
from `resolvedPrec`) or `Float`, the one branch here that picks the type
`aux_runAt` is generic over. -/
def dispatch (args : CliArgs) : IO Unit :=
  match args.ty with
  | "float" =>
    let toExact := if args.exact then some (fun x => let d := Binary64.toDyadic x
      s!"{d.mantissa}*2^{d.exponent}") else none
    aux_runAt (𝕋 := Float) args ExactDyadic.toFloat ExactDyadic.toFloatUnchecked id
      "binary64" toExact 53
  | _ =>
    let p := resolvedPrec args
    let toExact := if args.exact then
      some (fun (x : Dyadic p) => s!"{x.mantissa}*2^{x.exponent}") else none
    aux_runAt (𝕋 := Dyadic p) args (fun field d => d.toDyadicP field p)
      ExactDyadic.toDyadicPUnchecked dyadicToFloatApprox (precToFormat p) toExact p

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
