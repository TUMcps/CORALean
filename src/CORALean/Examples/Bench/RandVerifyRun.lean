import CORALean.Examples.Bench.Cli
import CORALean.Examples.Bench.GitInfo
import CORALean.Examples.Bench.RandVerifyLabel
import CORALean.Examples.Bench.RandVerifyParse
import CORALean.Examples.Bench.RandVerifyRecord

/-!
# `lake exe bench randverify --in FILE|DIR [--types L] [--algs L] [--dt Q] [--eta K] [--order R]`

EXPLORATORY: ARCH24 random verification instances (`ẋ = A x + B u`, `y = C x`, four unsafe boxes
in output space) under many number types. `--in` is an instance file, or a directory whose
`*.json` are all read (default `experiments/randverify`); every instance is run at every type of
`--types` (comma list of `randTypeKind` labels, default all of `defaultTypes`) and every
algorithm of `--algs` (`standard`, `wrappingfree`; default both), `--dt` (default `1/64`), `--eta`
(default `6`), `--order` (default `20`), and written to `<out>/randverify/<instance><tag>.json`.
`runFor` is the per-type half, `none` for a type this executable does not link, so one driver
serves `bench` and `bench-flint`.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench

open Lean (Json)


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

def aux_defaultTypes : String :=
  "dyadic12,dyadic16,dyadic24,dyadic32,dyadic53,dyadic64,dyadic128,dyadic256,dyadic1024,\
binary16,binary32,binary64,float,nearest,flint64,flint128,flint256,flint1024"

def aux_commaList (s : String) : List String :=
  (s.splitOn ",").map (·.trimAscii.toString) |>.filter (· ≠ "")

/-- The instance files `--in` names, sorted. -/
def aux_instanceFiles (path : System.FilePath) : IO (Array System.FilePath) := do
  if ← path.isDir then
    let es ← path.readDir
    pure (es.map (·.path) |>.filter (·.extension == some "json") |>.qsort
      (fun a b => a.toString < b.toString))
  else pure #[path]


-- =====================================  MAIN DEFINITION  ====================================== --

def runRandVerifyWith (args : CliArgs) (tag : String)
    (runFor : String → RandJob → Option (IO Json)) : IO Unit := do
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
  -- every instance at every type and algorithm, one output file each
  let mut skipped : List String := []
  for f in files do
    let text ← IO.FS.readFile f
    let j ← IO.ofExcept (Json.parse text |>.mapError fun e => s!"{f}: invalid JSON: {e}")
    let name := f.fileStem.getD f.toString
    let I ← IO.ofExcept (parseRandInstance name j |>.mapError fun e => s!"{f}: {e}")
    -- the records of this instance
    let mut records : Array Json := #[]
    for t in types do
      for alg in algs do
        match runFor t { inst := I, dt := dt, alg := alg, eta := eta, rho := rho } with
        | none => skipped := t :: skipped
        | some run =>
          -- run, say so, keep the record
          let r ← run
          let st := (r.getObjValAs? String "status").toOption.getD "?"
          let ver := (r.getObjVal? "verified").toOption.map (·.compress) |>.getD "?"
          IO.println s!"randverify: {name} {t} {alg.name}: {st}, verified {ver}"
          records := records.push r
    -- the meta and the file
    let metaJ := Json.mkObj
      [ ("experiment", Json.str "randverify"), ("exploratory", Json.bool true),
        ("gitCommit", Json.str (← gitCommit)), ("leanVersion", Json.str (← leanVersion)),
        ("types", Lean.toJson types), ("algs", Lean.toJson (algs.map RandAlg.name)),
        ("dt", Json.str dt), ("eta", Lean.toJson eta), ("order", Lean.toJson rho),
        ("instance", Json.mkObj [("name", Json.str name), ("meta", I.extra)]) ]
    let dir := System.FilePath.mk args.outDir / "randverify"
    IO.FS.createDirAll dir
    let out := dir / s!"{name}{tag}.json"
    IO.FS.writeFile out (Json.mkObj [("meta", metaJ), ("results", Json.arr records)]).pretty
    IO.println s!"randverify: wrote {out} ({records.size} records)"
  if !skipped.isEmpty then
    IO.eprintln s!"randverify: skipped type(s) {skipped.eraseDups.reverse}, not available in this \
      executable"

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
