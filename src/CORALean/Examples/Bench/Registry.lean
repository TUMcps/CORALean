import CORALean.ContDynamics.LinearSys.Operations.ReachFloat
import CORALean.ContDynamics.LinearSys.Operations.ReachRecursiveFloat
import CORALean.ContDynamics.LinearSys.Operations.ReachTimePointFloat
import CORALean.Examples.Bench.Cli
import CORALean.Examples.Bench.ContRollout
import CORALean.Examples.Bench.NearestUnsound.API
import CORALean.Examples.Bench.Nn
import CORALean.Examples.Bench.Output
import CORALean.Global.Float.Instances.Binary64.API
import CORALean.Global.Float.Instances.Dyadic.API

/-!
# `dtdemo`, `headline-a`, `headline-b`, `exp2-timepoint`

`dispatch` is the one place `main` calls into; every experiment name it knows
goes through `runAt`, generic in the scalar `𝕋`, instantiated once at
`Dyadic p` and once at `Float` by `dispatch` itself. `dtdemo` is
`LinearSysDT.reach` on `Rollout.buildSystem`'s placeholder Euler
discretization. The other three run the verified continuous-time algorithms
(`ContRollout.buildContSystem`'s exact `A`, `X0`) through `aux_runTiTp`, shared
over the one difference between them, `aux_algoHeadlineA`/`B`/`Exp2` -- which
call of `reachFloat`/`reachTimePointFloat`/`reachRecursiveFloat` each is.

A `dyadic` run's significand width, `resolvedPrec`, is `--prec` if given (a
raw bit count, for a precision none of the five `--format` labels name), else
`--format` mapped through `formatToPrec` (already validated by `parseArgs`),
else `53` -- `binary64`, so the default agrees with native `Float`.
-/

-- Authors:       Tobias Ladner
-- Written:       25-September-2026
-- Last update:   27-September-2026
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


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Scheme (a), wrapping-free: `reachFloat`'s time-interval windows beside
`reachTimePointFloat`'s time-point sets at the same `X₀`, `dt`, `eta`, `rho`,
`N` -- `headline-a`'s whole algorithm call, both `some` or the pair is `none`. -/
def aux_algoHeadlineA {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]
    (sys : LinearSys 𝕋 2) (X0 : Zonotope 𝕋 2) (dt : 𝕋) (cfg : HeadlineConfig) :
    Unit → Option (List (Zonotope 𝕋 2) × List (Zonotope 𝕋 2)) :=
  fun _ => match sys.reachFloat X0 dt cfg.eta cfg.rho cfg.steps,
      sys.reachTimePointFloat X0 dt cfg.eta cfg.steps with
    | some ti, some tp => some (ti, tp)
    | _, _ => none

/-- Scheme (b), recursive: `reachRecursiveFloat`'s own `(Rti, Rtp)` pair
directly -- `headline-b`'s whole algorithm call. -/
def aux_algoHeadlineB {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]
    (sys : LinearSys 𝕋 2) (X0 : Zonotope 𝕋 2) (dt : 𝕋) (cfg : HeadlineConfig) :
    Unit → Option (List (Zonotope 𝕋 2) × List (Zonotope 𝕋 2)) :=
  fun _ => sys.reachRecursiveFloat X0 dt cfg.eta cfg.rho cfg.steps

/-- Scheme (b) again, keeping only the time-point half -- `exp2-timepoint`'s
whole algorithm call, for the precision ablation at every `--format`. -/
def aux_algoExp2 {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]
    (sys : LinearSys 𝕋 2) (X0 : Zonotope 𝕋 2) (dt : 𝕋) (cfg : HeadlineConfig) :
    Unit → Option (List (Zonotope 𝕋 2) × List (Zonotope 𝕋 2)) :=
  fun _ => (sys.reachRecursiveFloat X0 dt cfg.eta cfg.rho cfg.steps).map fun (_, Rtp) => ([], Rtp)

/-- Loads the config, builds the continuous-time system, checks `eta` is
admissible, times `mkAlgo`'s closure over `reps` repetitions, and writes the
result -- `writeRunTiTp` on success, else `writeRunNone` and a nonzero exit. -/
def aux_runTiTp {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] (args : CliArgs)
    (inst : String → ExactDyadic → Except String 𝕋) (toD : 𝕋 → Float) (format : String)
    (toExact : Option (𝕋 → String)) (sig : ℕ) (experiment scheme : String)
    (mkAlgo : LinearSys 𝕋 2 → Zonotope 𝕋 2 → 𝕋 → HeadlineConfig →
      Unit → Option (List (Zonotope 𝕋 2) × List (Zonotope 𝕋 2))) :
    IO Unit := do
  let (configJ, cfg) ← loadConfig args.config
  let (sys, X0) ← match buildContSystem cfg inst with
    | .ok v => pure v
    | .error e => throw (IO.userError s!"{args.config}: {e}")
  let exact ← IO.ofExcept (parseExact cfg.dt)
  let dt ← match inst "dt" exact with
    | .ok v => pure v
    | .error e => throw (IO.userError e)
  let dtFloat ← match ExactDyadic.toFloat "dt" exact with
    | .ok v => pure v
    | .error e => throw (IO.userError e)
  let out := outPath args.outDir args.config experiment args.ty format
  -- checked once, cheaply, ahead of `mkAlgo`'s own (larger) call, for a clear "no order" reason
  match sys.reachOrderFloat dt dt cfg.eta with
  | none =>
    writeRunNone out experiment scheme args.ty format sig configJ
      s!"no admissible Taylor order (from max {cfg.eta} 2) found within the search bound"
    IO.eprintln s!"{experiment}: wrote {out}.json (status: none -- no admissible order)"
    IO.Process.exit 1
  | some etaUsed =>
    let reps := args.reps.getD cfg.reps
    let (samples, medianNs, lastR) ← timeAlgo toD (mkAlgo sys X0 dt cfg) reps
    match lastR with
    | none =>
      writeRunNone out experiment scheme args.ty format sig configJ
        s!"the algorithm returned none despite an admissible order eta = {etaUsed} -- \
          likely a window's squaring search failed"
      IO.eprintln s!"{experiment}: wrote {out}.json (status: none)"
      IO.Process.exit 1
    | some (ti, tp) =>
      writeRunTiTp out experiment scheme args.ty format sig configJ etaUsed cfg.rho cfg.steps
        samples medianNs toD toExact dtFloat ti.toArray tp.toArray
      IO.println s!"{experiment}: wrote {out}.json and {out}.csv ({ti.length} ti, \
        {tp.length} tp steps, median {medianNs} ns over {reps} rep(s), eta = {etaUsed})"

/-- `args.experiment`, run at whichever `𝕋` `dispatch` picked. -/
def aux_runAt {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] (args : CliArgs)
    (inst : String → ExactDyadic → Except String 𝕋) (instUnchecked : ExactDyadic → 𝕋)
    (toD : 𝕋 → Float) (format : String) (toExact : Option (𝕋 → String)) (sig : ℕ) :
    IO Unit :=
  match args.experiment with
  | "nn-float32" => runNnFloat32 args
  | "dtdemo" => runDtdemo args inst instUnchecked toD format toExact sig
  | "headline-a" =>
    aux_runTiTp args inst toD format toExact sig "headline-a" "wrapping-free" aux_algoHeadlineA
  | "headline-b" =>
    aux_runTiTp args inst toD format toExact sig "headline-b" "standard" aux_algoHeadlineB
  | "exp2-timepoint" =>
    aux_runTiTp args inst toD format toExact sig "exp2-timepoint" "standard" aux_algoExp2
  | other => do
    IO.eprintln s!"unknown experiment `{other}` -- one of dtdemo, headline-a, \
      headline-b, exp2-timepoint, nn-float32"
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

open CORALean.Bench.NearestUnsound in
/-- `--type nearest`, with NO guarantees: `NearestFloat`, or `NearestDyadic p` once
`--prec` or a `--format` other than `binary64` asks for one. The only code that
opens the unsound instances, and it runs the same `aux_runAt` as the others. -/
def dispatchNearest (args : CliArgs) : IO Unit :=
  match args.prec, args.format with
  | none, none | none, some "binary64" =>
    let toExact := if args.exact then some (fun (x : NearestFloat) =>
      let d := Binary64.toDyadic x.val; s!"{d.mantissa}*2^{d.exponent}") else none
    aux_runAt (𝕋 := NearestFloat) args (fun field d => (ExactDyadic.toFloat field d).map (⟨·⟩))
      (fun d => ⟨ExactDyadic.toFloatUnchecked d⟩) (·.val) "binary64" toExact 53
  | _, _ =>
    let p := resolvedPrec args
    let toExact := if args.exact then
      some (fun (x : NearestDyadic p) => s!"{x.val.mantissa}*2^{x.val.exponent}") else none
    aux_runAt (𝕋 := NearestDyadic p) args (fun field d => (d.toDyadicP field p).map (⟨·⟩))
      (fun d => ⟨ExactDyadic.toDyadicPUnchecked d⟩) (fun x => dyadicToFloatApprox x.val)
      (precToFormat p) toExact p

/-- Runs `args.experiment` at the scalar `args.ty` names -- `Dyadic p` (`p`
from `resolvedPrec`), `Float`, or the unsound `nearest` baseline, the one branch
here that picks the type `aux_runAt` is generic over. -/
def dispatch (args : CliArgs) : IO Unit :=
  match args.ty with
  | "float" =>
    let toExact := if args.exact then some (fun x => let d := Binary64.toDyadic x
      s!"{d.mantissa}*2^{d.exponent}") else none
    aux_runAt (𝕋 := Float) args ExactDyadic.toFloat ExactDyadic.toFloatUnchecked id
      "binary64" toExact 53
  | "nearest" => dispatchNearest args
  | _ =>
    let p := resolvedPrec args
    let toExact := if args.exact then
      some (fun (x : Dyadic p) => s!"{x.mantissa}*2^{x.exponent}") else none
    aux_runAt (𝕋 := Dyadic p) args (fun field d => d.toDyadicP field p)
      ExactDyadic.toDyadicPUnchecked dyadicToFloatApprox (precToFormat p) toExact p

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
