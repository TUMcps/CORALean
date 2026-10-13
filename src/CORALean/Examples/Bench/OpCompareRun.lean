import CORALean.Examples.Bench.Cli
import CORALean.Examples.Bench.FloatPrint
import CORALean.Examples.Bench.GitInfo
import CORALean.Examples.Bench.OpCompareCompute
import CORALean.Examples.Bench.OpCompareInput
import Lean.Data.Json

/-!
# `lake exe bench opcompare --in FILE [--out FILE]`

Reads `inputs.json`'s hex bit patterns, checks they round-trip through `IEEE .binary64`
unchanged, then computes `sum_v`, `sum_cancel`, `dot_vw`, `mtimes100` and `mtimes500` at all
five variants -- `hardware_nearest`, `hardware_down`/`_up` (native `Float`, `FloatOps`),
`ieee_down`/`_up` (`IEEE .binary64`, the same `FloatOps` class) -- and writes one compact JSON,
timed per quantity and variant. `--out`, elsewhere a results directory, is this file's own path
here, since `opcompare` writes one file rather than a `<config>/<experiment>/` tree; its default
is `experiments/matlab-ops/coralean_results.json`. A `hardware_down`/`_up` result equal to the
range guard's fixed bit pattern is counted as a NaN, past `Binary64`'s trusted range.
-/

-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench

open CORALean.Float (IEEE IEEEFormat)
open Lean (Json)


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

-- The range guard's fixed quiet-NaN bit pattern (`Binary64/Operations/InRange.lean`), hex.
def aux_nanHex : String := "7ff8000000000000"

/-- The five variants of a sum or dot product, each a thunk producing its hex string or the
reason it could not (`ieee64ToHex`'s overflow check). -/
def aux_sumThunks (xs : Array Float) (xsI : Array (IEEE IEEEFormat.binary64)) :
    List (String × (Unit → Except String String)) :=
  [ ("hardware_nearest", fun _ => pure (floatToHex (seqSumNearest xs))),
    ("hardware_down", fun _ => pure (floatToHex (seqSumFO true xs))),
    ("hardware_up", fun _ => pure (floatToHex (seqSumFO false xs))),
    ("ieee_down", fun _ => ieee64ToHex (seqSumFO true xsI)),
    ("ieee_up", fun _ => ieee64ToHex (seqSumFO false xsI)) ]

/-- `aux_sumThunks`'s dot-product counterpart. -/
def aux_dotThunks (xs ys : Array Float) (xsI ysI : Array (IEEE IEEEFormat.binary64)) :
    List (String × (Unit → Except String String)) :=
  [ ("hardware_nearest", fun _ => pure (floatToHex (seqDotNearest xs ys))),
    ("hardware_down", fun _ => pure (floatToHex (seqDotFO true xs ys))),
    ("hardware_up", fun _ => pure (floatToHex (seqDotFO false xs ys))),
    ("ieee_down", fun _ => ieee64ToHex (seqDotFO true xsI ysI)),
    ("ieee_up", fun _ => ieee64ToHex (seqDotFO false xsI ysI)) ]

/-- The five variants of `A * B`, `n × n`, each a thunk producing the row-major hex array. -/
def aux_mtimesThunks (numChunks n : Nat) (A B : Array Float)
    (AI BI : Array (IEEE IEEEFormat.binary64)) :
    List (String × (Unit → Except String (Array String))) :=
  [ ("hardware_nearest", fun _ => pure ((matMulNearest numChunks n A B).map floatToHex)),
    ("hardware_down", fun _ => pure ((matMulFO numChunks true n A B).map floatToHex)),
    ("hardware_up", fun _ => pure ((matMulFO numChunks false n A B).map floatToHex)),
    ("ieee_down", fun _ => (matMulFO numChunks true n AI BI).mapM ieee64ToHex),
    ("ieee_up", fun _ => (matMulFO numChunks false n AI BI).mapM ieee64ToHex) ]

/-- Runs every thunk of a scalar quantity, timed: the hex values object, the seconds-per-variant
object, and how many of the five came back the range guard's NaN. -/
def aux_runScalar (thunks : List (String × (Unit → Except String String))) :
    IO (Json × Json × Nat) := do
  let mut valsJ : List (String × Json) := []
  let mut timesJ : List (String × Json) := []
  let mut nanCount := 0
  for (name, f) in thunks do
    let t0 ← IO.monoNanosNow
    let hex ← IO.ofExcept (f ())
    let t1 ← IO.monoNanosNow
    if hex = aux_nanHex then nanCount := nanCount + 1
    valsJ := valsJ ++ [(name, Json.str hex)]
    timesJ := timesJ ++ [(name, floatToJson ((t1 - t0).toFloat / 1.0e9))]
  pure (Json.mkObj valsJ, Json.mkObj timesJ, nanCount)

/-- `aux_runScalar`'s matrix counterpart: each variant is a whole `n²` hex array. -/
def aux_runMatrix (thunks : List (String × (Unit → Except String (Array String)))) :
    IO (Json × Json × Nat) := do
  let mut valsJ : List (String × Json) := []
  let mut timesJ : List (String × Json) := []
  let mut nanCount := 0
  for (name, f) in thunks do
    let t0 ← IO.monoNanosNow
    let hexArr ← IO.ofExcept (f ())
    let t1 ← IO.monoNanosNow
    nanCount := nanCount + (hexArr.filter (· = aux_nanHex)).size
    valsJ := valsJ ++ [(name, Json.arr (hexArr.map Json.str))]
    timesJ := timesJ ++ [(name, floatToJson ((t1 - t0).toFloat / 1.0e9))]
  pure (Json.mkObj valsJ, Json.mkObj timesJ, nanCount)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `--in FILE`'s inputs, decoded and round-trip checked, run at every quantity and variant,
written compact to `--out FILE` (default `experiments/matlab-ops/coralean_results.json`). -/
def runOpCompare (args : CliArgs) : IO Unit := do
  let inFile := args.inFile.getD "experiments/matlab-ops/inputs.json"
  let outFile : System.FilePath := if args.outDir = "experiments/results" then
    "experiments/matlab-ops/coralean_results.json" else System.FilePath.mk args.outDir
  IO.println s!"opcompare: reading {inFile}"
  let hexIn ← loadInputHex inFile
  IO.ofExcept (checkRoundTrip hexIn.allHex)
  IO.println s!"opcompare: round-trip check passed on {hexIn.allHex.size} hex tokens"
  let floatsIn ← IO.ofExcept (decodeInputs hexIn)
  -- every array, also at `IEEE .binary64` -- exact, `floatToIEEE64` loses nothing
  let v1e4I := floatsIn.v1e4.map floatToIEEE64
  let w1e4I := floatsIn.w1e4.map floatToIEEE64
  let cancelI := floatsIn.cancel.map floatToIEEE64
  let A100I := floatsIn.A100.map floatToIEEE64
  let B100I := floatsIn.B100.map floatToIEEE64
  let A500I := floatsIn.A500.map floatToIEEE64
  let B500I := floatsIn.B500.map floatToIEEE64
  -- one `Task` per row is wasteful at `n = 100`; both matrices just use every core
  let cores ← coreCount
  let nc100 := max 1 (min cores 100)
  let nc500 := max 1 (min cores 500)
  IO.println "opcompare: sum_v"
  let (sumVJ, sumVT, sumVN) ← aux_runScalar (aux_sumThunks floatsIn.v1e4 v1e4I)
  IO.println "opcompare: sum_cancel"
  let (sumCJ, sumCT, sumCN) ← aux_runScalar (aux_sumThunks floatsIn.cancel cancelI)
  IO.println "opcompare: dot_vw"
  let (dotJ, dotT, dotN) ← aux_runScalar (aux_dotThunks floatsIn.v1e4 floatsIn.w1e4 v1e4I w1e4I)
  IO.println s!"opcompare: mtimes100 ({nc100} tasks)"
  let (m100J, m100T, m100N) ← aux_runMatrix
    (aux_mtimesThunks nc100 100 floatsIn.A100 floatsIn.B100 A100I B100I)
  IO.println s!"opcompare: mtimes500 ({nc500} tasks)"
  let (m500J, m500T, m500N) ← aux_runMatrix
    (aux_mtimesThunks nc500 500 floatsIn.A500 floatsIn.B500 A500I B500I)
  -- the exact shape the task asks for: five quantities, `meta.git`/`meta.timings_s` beside them
  let commit ← gitCommit
  let metaJ := Json.mkObj
    [ ("git", Json.str commit),
      ("timings_s", Json.mkObj
        [ ("sum_v", sumVT), ("sum_cancel", sumCT), ("dot_vw", dotT),
          ("mtimes100", m100T), ("mtimes500", m500T) ]) ]
  let doc := Json.mkObj
    [ ("sum_v", sumVJ), ("sum_cancel", sumCJ), ("dot_vw", dotJ),
      ("mtimes100", m100J), ("mtimes500", m500J), ("meta", metaJ) ]
  match outFile.parent with
  | some dir => IO.FS.createDirAll dir
  | none => pure ()
  IO.FS.writeFile outFile doc.compress
  let nanTotal := sumVN + sumCN + dotN + m100N + m500N
  if nanTotal > 0 then
    IO.eprintln s!"opcompare: {nanTotal} hardware_down/up result(s) are NaN (past binary64's \
      trusted range)"
  IO.println s!"opcompare: wrote {outFile}"

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
