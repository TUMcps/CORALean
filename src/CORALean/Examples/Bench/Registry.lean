import CORALean.ContDynamics.LinearSys.Operations.ReachFloatChecked
import CORALean.ContDynamics.LinearSys.Operations.ReachTimePointWrappingFreeFloatChecked
import CORALean.ContDynamics.LinearSys.Operations.ReachWrappingFreeFloatChecked
import CORALean.Examples.Bench.Cli
import CORALean.Examples.Bench.ContRollout
import CORALean.Examples.Bench.FirstStepRun
import CORALean.Examples.Bench.FirstStepTypes
import CORALean.Examples.Bench.Ieee
import CORALean.Examples.Bench.Mnist
import CORALean.Examples.Bench.Config
import CORALean.Examples.Bench.Format
import CORALean.Examples.Bench.NearestUnsound.Instances
import CORALean.Examples.Bench.NearestUnsound.NearestDyadic
import CORALean.Examples.Bench.NearestUnsound.NearestFloat
import CORALean.Examples.Bench.NumberType
import CORALean.Examples.Bench.Rational
import CORALean.Examples.Bench.Rollout
import CORALean.Examples.Bench.Timing
import CORALean.Global.Float.Instances.Binary64.Instances
import CORALean.Global.Float.Instances.Dyadic.Instances
import CORALean.Global.Float.Instances.FixedPoint.Instances
import CORALean.Global.Float.Instances.IEEE.Instances
import CORALean.Examples.Bench.Nn
import CORALean.Examples.Bench.OpCompareRun
import CORALean.Examples.Bench.Output
import CORALean.Examples.Bench.RandVerifyFamily
import CORALean.Examples.Bench.RandVerifyRun
import CORALean.Examples.Bench.RandVerifyTypes

/-!
# `dtdemo`, `headline-a`, `headline-b`, `exp2-timepoint`

`dispatch` is the one place `main` calls into; every experiment name it knows goes through `runAt`,
generic in the scalar `𝕋`, instantiated once at `Dyadic p` and once at `Float`. `dtdemo` is
`LinearSysDT.reach` on `Rollout.buildSystem`'s placeholder Euler discretization. The other three
run the verified continuous-time algorithms (`ContRollout.buildContSystem`) through `aux_runTiTp`;
a result holding a NaN is not reported. A `dyadic` run's significand width, `resolvedPrec`, is
`--prec` if given, else `--format` mapped through `formatToPrec`, else `53`, so the default agrees
with native `Float`. `opcompare`, `firststep`, `randverify` and `randverify-family` are unrelated,
intercepted ahead of `runAt`: each takes every scalar it needs from its own files.

## Inputs
* `args` – parsed command line

## Output
* significand width of the run
-/

-- Authors:       Claude Opus 5.5
-- Written:       25-September-2026
-- Last update:   01-October-2026
-- Reviewed:      ---


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
def runDtdemo {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] (args : CliArgs)
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
  let (samples, medianNs, _checksum, unchecked) ← timeRollout toD S cfg.rho cfg.steps reps
  -- the rollout is reported only if no float of it is a NaN, as the `…Checked` calls do
  let steps ← match ifNoNaN (𝕋 := 𝕋) unchecked with
    | some ok => pure ok
    | none => throw (IO.userError s!"{args.config}: dtdemo: a float of the result is a NaN")
  let out := outPath args.outDir args.config "dtdemo" args.ty format
  writeRun out "dtdemo" "reach" args.ty format sig configJ cfg.eta samples medianNs toD
    toExact dtFloat steps
  IO.println s!"dtdemo: wrote {out}.json and {out}.csv ({steps.size} steps, median \
    {medianNs} ns over {reps} rep(s))"


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The config's `X0` and horizon as CORA's `params`: `tFinal = steps · dt`, exactly the
config's own reading of `steps` (`headline_*.json`'s `steps_comment`), so the run derives
`steps` back from it, `dt` being exact in `𝕋`. -/
def aux_params {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] (X0 : Zonotope (Vec 𝕋 2))
    (dt : 𝕋) (cfg : HeadlineConfig) : Reach.Params (Zonotope (Vec 𝕋 2)) ℚ :=
  { X₀ := X0, tFinal := cfg.steps * ToRat.toRat dt }

/-- The config's `dt`, `eta` and `rho` as CORA's `options`, under CORA's own names. -/
def aux_options {𝕋 : Type} (dt : 𝕋) (cfg : HeadlineConfig) : LinearSys.ReachOptions 𝕋 :=
  { Δt := dt, η := cfg.eta, ρ := cfg.rho }

/-- Scheme (a), wrapping-free: `reachWrappingFreeFloat`'s time-interval windows beside
`reachTimePointWrappingFreeFloat`'s time-point sets at the same `X₀`, `dt`, `eta`, `rho`,
`N` -- `headline-a`'s whole algorithm call, both `some` or the pair is `none`. -/
def aux_algoHeadlineA {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]
    (sys : LinearSys 𝕋 2) (X0 : Zonotope (Vec 𝕋 2)) (dt : 𝕋) (cfg : HeadlineConfig) :
    Unit → Option (List (Zonotope (Vec 𝕋 2)) × List (Zonotope (Vec 𝕋 2))) :=
  fun _ => match sys.reachWrappingFreeFloatChecked (aux_params X0 dt cfg) (aux_options dt cfg),
      sys.reachTimePointWrappingFreeFloatChecked (aux_params X0 dt cfg) (aux_options dt cfg) with
    | some ti, some tp => some (ti, tp)
    | _, _ => none

/-- Scheme (b), recursive: `reachFloat`'s own `(Rti, Rtp)` pair
directly -- `headline-b`'s whole algorithm call. -/
def aux_algoHeadlineB {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]
    (sys : LinearSys 𝕋 2) (X0 : Zonotope (Vec 𝕋 2)) (dt : 𝕋) (cfg : HeadlineConfig) :
    Unit → Option (List (Zonotope (Vec 𝕋 2)) × List (Zonotope (Vec 𝕋 2))) :=
  fun _ => sys.reachFloatChecked (aux_params X0 dt cfg) (aux_options dt cfg)

/-- Scheme (b) again, keeping only the time-point half -- `exp2-timepoint`'s
whole algorithm call, for the precision ablation at every `--format`. -/
def aux_algoExp2 {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]
    (sys : LinearSys 𝕋 2) (X0 : Zonotope (Vec 𝕋 2)) (dt : 𝕋) (cfg : HeadlineConfig) :
    Unit → Option (List (Zonotope (Vec 𝕋 2)) × List (Zonotope (Vec 𝕋 2))) :=
  fun _ => (sys.reachFloatChecked (aux_params X0 dt cfg) (aux_options dt cfg)).map
    fun (_, Rtp) => ([], Rtp)

/-- Loads the config, builds the continuous-time system, checks `eta` is
admissible, times `mkAlgo`'s closure over `reps` repetitions, and writes the
result -- `writeRunTiTp` on success, else `writeRunNone` and a nonzero exit. -/
def aux_runTiTp {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] (args : CliArgs)
    (inst : String → ExactDyadic → Except String 𝕋) (toD : 𝕋 → Float) (format : String)
    (toExact : Option (𝕋 → String)) (sig : ℕ) (experiment scheme : String)
    (mkAlgo : LinearSys 𝕋 2 → Zonotope (Vec 𝕋 2) → 𝕋 → HeadlineConfig →
      Unit → Option (List (Zonotope (Vec 𝕋 2)) × List (Zonotope (Vec 𝕋 2))))
    (nt : NumberType 𝕋 := {}) : IO Unit := do
  let (configJ, cfg) ← loadConfig args.config
  let exact ← IO.ofExcept (parseExact cfg.dt)
  let out := outPath args.outDir args.config experiment args.ty format
  match buildContSystem cfg inst, inst "dt" exact with
  | .error e, _ | .ok _, .error e =>
    -- a format that cannot hold the config is this run's outcome; at any other type, an error
    if args.ty = "ieee" then
      writeRunNone out experiment scheme args.ty format sig configJ e nt.metaFields
        "unrepresentable"
      IO.eprintln s!"{experiment}: wrote {out}.json (status: unrepresentable -- {e})"
    else throw (IO.userError s!"{args.config}: {e}")
  | .ok (sys, X0), .ok dt =>
  let dtFloat ← match ExactDyadic.toFloat "dt" exact with
    | .ok v => pure v
    | .error e => throw (IO.userError e)
  -- checked once, cheaply, ahead of `mkAlgo`'s own (larger) call, for a clear "no order" reason
  match sys.reachOrderFloat dt dt cfg.eta with
  | none =>
    writeRunNone out experiment scheme args.ty format sig configJ
      s!"no admissible Taylor order (from max {cfg.eta} 2) found within the search bound"
      nt.metaFields
    IO.eprintln s!"{experiment}: wrote {out}.json (status: none -- no admissible order)"
    IO.Process.exit 1
  | some etaUsed =>
    let reps := args.reps.getD cfg.reps
    let (samples, medianNs, lastR) ← timeAlgo toD (mkAlgo sys X0 dt cfg) reps
    match lastR with
    | none =>
      writeRunNone out experiment scheme args.ty format sig configJ
        s!"the algorithm returned none despite an admissible order eta = {etaUsed} -- \
          likely a window's squaring search failed, or a float of the result is a NaN \
          (the `…Checked` calls report no result holding one)" nt.metaFields
      IO.eprintln s!"{experiment}: wrote {out}.json (status: none)"
      IO.Process.exit 1
    | some (ti, tp) =>
      writeRunTiTp out experiment scheme args.ty format sig configJ etaUsed cfg.rho cfg.steps
        samples medianNs toD toExact dtFloat ti.toArray tp.toArray nt
      IO.println s!"{experiment}: wrote {out}.json and {out}.csv ({ti.length} ti, \
        {tp.length} tp steps, median {medianNs} ns over {reps} rep(s), eta = {etaUsed})"

/-- `args.experiment`, run at whichever `𝕋` `dispatch` picked. -/
def runAt {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] (args : CliArgs)
    (inst : String → ExactDyadic → Except String 𝕋) (instUnchecked : ExactDyadic → 𝕋)
    (toD : 𝕋 → Float) (format : String) (toExact : Option (𝕋 → String)) (sig : ℕ)
    (nt : NumberType 𝕋 := {}) : IO Unit :=
  match args.experiment with
  | "nn-float32" => runNnFloat32 args
  | "nn-mnist" => runNnMnist args inst instUnchecked toD format toExact sig nt
  | "dtdemo" => runDtdemo args inst instUnchecked toD format toExact sig
  | "headline-a" =>
    aux_runTiTp args inst toD format toExact sig "headline-a" "wrapping-free" aux_algoHeadlineA nt
  | "headline-b" =>
    aux_runTiTp args inst toD format toExact sig "headline-b" "standard" aux_algoHeadlineB nt
  | "exp2-timepoint" =>
    aux_runTiTp args inst toD format toExact sig "exp2-timepoint" "standard" aux_algoExp2 nt
  | other => do
    IO.eprintln s!"unknown experiment `{other}` -- one of dtdemo, headline-a, \
      headline-b, exp2-timepoint, nn-float32, nn-mnist"
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

/-- The decimal digit count a `fixed` run picks: `--digits` if given, else `4`. -/
def resolvedDigits (args : CliArgs) : ℕ := args.digits.getD 4

open CORALean.Bench.NearestUnsound in
/-- `--type nearest`, with NO guarantees: `NearestFloat`, or `NearestDyadic p` once
`--prec` or a `--format` other than `binary64` asks for one. The only code that
opens the unsound instances, and it runs the same `runAt` as the others. -/
def dispatchNearest (args : CliArgs) : IO Unit :=
  match args.prec, args.format with
  | none, none | none, some "binary64" =>
    let toExact := if args.exact then some (fun (x : NearestFloat) =>
      let d := Binary64.toDyadic x.val; s!"{d.mantissa}*2^{d.exponent}") else none
    runAt (𝕋 := NearestFloat) args (fun field d => (ExactDyadic.toFloat field d).map (⟨·⟩))
      (fun d => ⟨ExactDyadic.toFloatUnchecked d⟩) (·.val) "binary64" toExact 53
      { description := "round-to-nearest binary64 (native Float, unsound)" }
  | _, _ =>
    let p := resolvedPrec args
    let toExact := if args.exact then
      some (fun (x : NearestDyadic p) => s!"{x.val.mantissa}*2^{x.val.exponent}") else none
    runAt (𝕋 := NearestDyadic p) args (fun field d => (d.toDyadicP field p).map (⟨·⟩))
      (fun d => ⟨ExactDyadic.toDyadicPUnchecked d⟩) (fun x => dyadicToFloatApprox x.val)
      (precToFormat p) toExact p
      { description := s!"round-to-nearest {dyadicDescription (precToFormat p) p}, unsound" }

/-- `--type ieee`: `IEEE fmt` at the format `--format` names, `binary64` by default; `--prec`
does not apply, a format being more than a width. -/
def dispatchIeee (args : CliArgs) : IO Unit := do
  let label := args.format.getD "binary64"
  let fmt ← IO.ofExcept (ieeeFormat label)
  let toExact := if args.exact then
    some (fun (x : IEEE fmt) => s!"{x.mantissa}*2^{x.exponent}") else none
  runAt (𝕋 := IEEE fmt) args (fun field d => d.toIEEE field fmt) ExactDyadic.toIEEEUnchecked
    ieeeToFloatApprox label toExact fmt.p (ieeeNumberType label fmt)

/-- Runs `args.experiment` at the scalar `args.ty` names -- `Dyadic p`, `IEEE fmt`,
`Float`, `nearest` or `FixedPoint f` -- the one branch here that picks the type
`runAt` is generic over; `opcompare` is intercepted ahead of it, see above. -/
def dispatch (args : CliArgs) : IO Unit :=
  if args.experiment = "opcompare" then runOpCompare args else
  if args.experiment = "firststep" then runFirstStepWith args "results" firstStepBenchRecord else
  if args.experiment = "randverify" then runRandVerifyWith args "" randVerifyBenchRecord else
  if args.experiment = "randverify-family" then runRandVerifyFamily args else
  match args.ty with
  | "float" =>
    let toExact := if args.exact then some (fun x => let d := Binary64.toDyadic x
      s!"{d.mantissa}*2^{d.exponent}") else none
    runAt (𝕋 := Float) args ExactDyadic.toFloat ExactDyadic.toFloatUnchecked id
      "binary64" toExact 53
      { description := "hardware binary64 (native Float, trusted, NaN outside the normal range)" }
  | "nearest" => dispatchNearest args
  | "fixed" =>
    let f := resolvedDigits args
    let toExact := if args.exact then
      some (fun (x : FixedPoint f) => s!"{x.m}e-{x.d}") else none
    -- `format`/`significand_bits`, named for `Dyadic`, carry `"decimal<f>"`/`f` here.
    runAt (𝕋 := FixedPoint f) args (fun field d => d.toFixedPoint field f)
      ExactDyadic.toFixedPointUnchecked fixedPointToFloatApprox s!"decimal{f}" toExact f
      { description := s!"decimal fixed point, {f} fractional digits" }
  | "ieee" => dispatchIeee args
  | _ =>
    let p := resolvedPrec args
    let toExact := if args.exact then
      some (fun (x : Dyadic p) => s!"{x.mantissa}*2^{x.exponent}") else none
    runAt (𝕋 := Dyadic p) args (fun field d => d.toDyadicP field p)
      ExactDyadic.toDyadicPUnchecked dyadicToFloatApprox (precToFormat p) toExact p
      { description := dyadicDescription (precToFormat p) p }

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
