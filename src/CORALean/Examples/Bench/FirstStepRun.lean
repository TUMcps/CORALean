import CORALean.Examples.Bench.Cli
import CORALean.Examples.Bench.Config
import CORALean.Examples.Bench.FirstStepInput
import CORALean.Examples.Bench.GitInfo
import Lean.Data.Json

/-!
# `lake exe bench firststep --in FILE [--out DIR]`

The first time-interval enclosure `R_0` and time-point set `X_1` of the headline spiral under
many number formats, for the paper's qualitative figure. `--in` is `FirstStepInput`'s file
(default `experiments/firststep/configs.json`); every run it names is taken at every `dt` it
names, one `FirstStepRecord.firstStepRecord` each, and the lot written to
`<out>/firststep/<tag>.json` (`--out` defaults to `experiments/results`), `meta` beside
`results`. `recordFor` is the per-type half, `none` for a run this executable cannot make --
a `flint` run, which only `bench-flint` links -- so one driver serves both executables.

## Inputs
* `args` – parsed command line
* `tag` – output file tag
* `recordFor` – record builder per configuration and run

## Output
* the first-step records are written to the output directory
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench

open Lean (Json)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Runs every `(run, dt)` of the input through `recordFor`, writes `<out>/firststep/<tag>.json`,
and says on stderr which runs were skipped. -/
def runFirstStepWith (args : CliArgs) (tag : String)
    (recordFor : HeadlineConfig → FirstStepRun → String → Option Json) : IO Unit := do
  let inFile := args.inFile.getD "experiments/firststep/configs.json"
  let (inJ, inp) ← loadFirstStepInput inFile
  let (cfgJ, cfg) ← loadConfig inp.baseConfig
  -- every (run, dt) pair, in the file's order
  let mut records : Array Json := #[]
  let mut skipped : Array String := #[]
  for run in inp.runs do
    for dt in inp.dts do
      match recordFor cfg run dt with
      | some r => records := records.push r
      | none => skipped := skipped.push s!"{run.ty}"
  if skipped.size > 0 then
    IO.eprintln s!"firststep: skipped {skipped.size} record(s) of type {skipped.toList.eraseDups}, \
      not available in this executable"
  let metaJ := Json.mkObj
    [ ("experiment", Json.str "firststep"),
      ("gitCommit", Json.str (← gitCommit)),
      ("leanVersion", Json.str (← leanVersion)),
      ("input", inJ), ("config", cfgJ) ]
  let out : System.FilePath := System.FilePath.mk args.outDir / "firststep" / s!"{tag}.json"
  IO.FS.createDirAll (System.FilePath.mk args.outDir / "firststep")
  IO.FS.writeFile out (Json.mkObj [("meta", metaJ), ("results", Json.arr records)]).pretty
  IO.println s!"firststep: wrote {out} ({records.size} records)"

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
