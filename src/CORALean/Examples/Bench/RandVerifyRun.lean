import CORALean.Examples.Bench.Cli
import CORALean.Examples.Bench.GitInfo
import CORALean.Examples.Bench.RandVerifyLabel
import CORALean.Examples.Bench.RandVerifyParse
import CORALean.Examples.Bench.RandVerifyRecord
import CORALean.Examples.Bench.RandVerifySameSystem

/-!
# `lake exe bench randverify --in FILE|DIR [--types L] [--algs L] [--dt Q] [--eta K] [--order R]`

EXPLORATORY: ARCH24 random verification instances (`ẋ = A x + B u`, `y = C x`, four unsafe boxes in
output space) under many number types. `--in` is an instance file, or a directory whose `*.json`
are all read (default `experiments/randverify`); every instance is run at every type of `--types`
and every algorithm of `--algs` (`standard`, `wrappingfree`), `--dt` (default `1/64`), `--eta`
(default `6`), `--order` (default `20`), and written to `<out>/randverify/<instance><tag>.json`.
Instances stating the same system (`RandInstance.sameSystem`) are reached once per type and
algorithm and checked together. `runFor` is the per-type half, `none` for a type this executable
does not link.

## Inputs
* `args` – parsed command line
* `tag` – output file tag
* `runFor` – per-type runner

## Output
* the instances are run and written
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       01-October-2026
-- Last update:   01-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench

open Lean (Json)


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

private def aux_defaultTypes : String :=
  "dyadic12,dyadic16,dyadic24,dyadic32,dyadic53,dyadic64,dyadic128,dyadic256,dyadic1024,\
binary16,binary32,binary64,hardware,nearest,flint64,flint128,flint256,flint1024"

private def aux_commaList (s : String) : List String :=
  (s.splitOn ",").map (·.trimAscii.toString) |>.filter (· ≠ "")

/-- The instance files `--in` names, sorted. -/
private def aux_instanceFiles (path : System.FilePath) : IO (Array System.FilePath) := do
  if ← path.isDir then
    let es ← path.readDir
    pure (es.map (·.path) |>.filter (·.extension == some "json") |>.qsort
      (fun a b => a.toString < b.toString))
  else pure #[path]


-- =====================================  MAIN DEFINITION  ====================================== --

def runRandVerifyWith (args : CliArgs) (tag : String)
    (runFor : String → RandJob → Array RandInstance → Option (IO (Array Json))) : IO Unit := do
  -- the instances, types and algorithms to run
  let files ← aux_instanceFiles (System.FilePath.mk (args.inFile.getD "experiments/randverify"))
  let types := aux_commaList (args.types.getD aux_defaultTypes)
  for t in types do
    if (randTypeKind t).isNone then throw (IO.userError s!"randverify: `{t}` is no number type")
  let algs ← (aux_commaList (args.algs.getD "standard,wrappingfree")).mapM fun a =>
    match RandAlg.ofString? a with
    | some alg => pure alg
    | none => throw (IO.userError s!"randverify: `{a}` is `standard` or `wrappingfree`")
  let dt := args.dt.getD "1/64"
  let eta := args.eta.getD 6
  let rho := args.order.getD 20
  let mut insts : Array RandInstance := #[]
  for f in files do
    let text ← IO.FS.readFile f
    let j ← IO.ofExcept (Json.parse text |>.mapError fun e => s!"{f}: invalid JSON: {e}")
    let name := f.fileStem.getD f.toString
    insts := insts.push (← IO.ofExcept (parseRandInstance name j |>.mapError fun e => s!"{f}: {e}"))
  -- instances stating the same system share one reach per type and algorithm
  let groups := insts.foldl (fun (gs : Array (Array RandInstance)) I =>
    match gs.findIdx? (fun g => (g.getD 0 I).sameSystem I) with
    | some k => gs.modify k (·.push I)
    | none => gs.push #[I]) #[]
  let mut skipped : List String := []
  for g in groups do
    let I0 := g.getD 0 (insts.getD 0 default)
    IO.println s!"randverify: {g.size} instance(s) share the system of {I0.name}"
    -- the records of this group, per instance
    let mut records : Array (Array Json) := g.map fun _ => #[]
    for t in types do
      for alg in algs do
        match runFor t { inst := I0, dt := dt, alg := alg, eta := eta, rho := rho } g with
        | none => skipped := t :: skipped
        | some run =>
          -- run, say so, keep the records
          let rs ← run
          for (r, k) in rs.zipIdx do
            let st := (r.getObjValAs? String "status").toOption.getD "?"
            let ver := (r.getObjVal? "verified").toOption.map (·.compress) |>.getD "?"
            IO.println s!"randverify: {(g.getD k I0).name} {t} {alg.name}: {st}, verified {ver}"
            records := records.modify k (·.push r)
    -- the meta and the file, one per instance
    for (I, rs) in g.zip records do
      let metaJ := Json.mkObj
        [ ("experiment", Json.str "randverify"), ("exploratory", Json.bool true),
          ("gitCommit", Json.str (← gitCommit)), ("leanVersion", Json.str (← leanVersion)),
          ("types", Lean.toJson types), ("algs", Lean.toJson (algs.map RandAlg.name)),
          ("dt", Json.str dt), ("eta", Lean.toJson eta), ("order", Lean.toJson rho),
          ("instance", Json.mkObj [("name", Json.str I.name), ("meta", I.extra)]) ]
      let dir := System.FilePath.mk args.outDir / "randverify"
      IO.FS.createDirAll dir
      let out := dir / s!"{I.name}{tag}.json"
      IO.FS.writeFile out (Json.mkObj [("meta", metaJ), ("results", Json.arr rs)]).pretty
      IO.println s!"randverify: wrote {out} ({rs.size} records)"
  if !skipped.isEmpty then
    IO.eprintln s!"randverify: skipped type(s) {skipped.eraseDups.reverse}, not available in this \
      executable"

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
