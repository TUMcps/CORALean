import CORALean.Examples.Bench.Cli
import CORALean.Examples.Bench.FloatPrint
import CORALean.Examples.Bench.GitInfo
import CORALean.Examples.Bench.MnistNetwork
import CORALean.Examples.Bench.NumberType
import CORALean.Examples.Bench.Timing
import CORALean.Global.Float.Instances.Binary64.API
import CORALean.Global.Float.Instances.Dyadic.API

/-!
# `lake exe bench nn-mnist --net small|medium|large --type dyadic|float [...]`

The rounding-error ablation: how much sound enclosure radius CORALean's
`NeuralNetwork.enclose` accumulates through a real MNIST classifier, at
several precisions, propagating float boxes (`Float.Interval (Vec 𝕋 n)`) --
`MnistNetwork.lean`'s own docstring on `runLayers` says why a box and not a
zonotope. This file runs `--images` images (default `100`) through `--net`'s
network, `--reps` times each (default `1`), and writes
`<out>/nn-mnist/<net>/<type>[-<format>].json` and `<...>-layers.dat`.

Per image: `predicted` is the argmax of the propagated box's own midpoint;
`certified` is `ltStrict` between the box's bounds, sound and one-ulp
-margined, not a comparison of the printed doubles. A box has no generators
to separate from rounding error, so `error_radius` and `total_radius` are the
same width, both reported for the same JSON shape a zonotope run would have
used; `accuracy` (`predicted = label`) is for context only. At a type with a
range, an image any layer of which stores a value past it is `overflow` and not
certified, and `summary.overflowed_images` counts them.
-/

-- Authors:       Claude Opus 5.5
-- Written:       27-September-2026
-- Last update:   28-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench

open CORALean CORALean.Float ContSet Float.FloatOps Float.SoundFloatArithmetic
open Lean (Json)
open CORALean.Bench.Mnist (MnistAffine MnistImage parseMnistNet parseMnistData finalDim
  inputBox runReport meanRadius)

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]

/-- `--net`'s converted file, one of the three VNN-COMP `mnistfc` networks --
see `experiments/nn/mnist/SOURCES.md`. -/
def netFile : String → Except String System.FilePath
  | "small" => pure "experiments/nn/mnist/nets/small.txt"
  | "medium" => pure "experiments/nn/mnist/nets/medium.txt"
  | "large" => pure "experiments/nn/mnist/nets/large.txt"
  | other => throw s!"`--net` is `small`, `medium` or `large`, not `{other}`"

def dataFile : System.FilePath := "experiments/nn/mnist/data/mnist_test_first100.txt"


/-! ## Per-image metrics -/

/-- The index of the greatest entry -- `xs` is never empty here, every network
having at least one output. -/
def argmaxFloat (xs : Array Float) : ℕ := Id.run do
  let mut best := 0
  let mut bestVal := xs.getD 0 (-(1.0 / 0.0))
  for i in [0:xs.size] do
    let v := xs.getD i (-(1.0 / 0.0))
    if v > bestVal then
      bestVal := v
      best := i
  pure best

/-- `sup i - inf i`, max over every coordinate -- `Output.lean`'s own
"radius", read off whichever box (`E` alone, or the whole hull) the caller
passes, as an array of doubles rather than a `Float.Interval`. -/
def maxRadiusArr (los his : Array Float) : Float :=
  (Array.zipWith (fun l h => h - l) los his).foldl max 0.0

/-- One image's record: label, the propagated centre's own class, whether the
enclosure certifies it against every other logit, both radii, and the ten
logit bounds (as doubles) for a reader who wants them. -/
structure ImageResult where
  label : ℕ
  predicted : ℕ
  certified : Bool
  errorRadius : Float
  totalRadius : Float
  lo : Array Float
  hi : Array Float
  timeNs : ℕ
  overflow : Bool := false

def ImageResult.json (r : ImageResult) : Json :=
  Json.mkObj <| (if r.overflow then [("overflow", Json.bool true)] else []) ++
    [ ("label", Lean.toJson r.label),
      ("predicted", Lean.toJson r.predicted),
      ("certified", Json.bool r.certified),
      ("error_radius", floatToJson r.errorRadius),
      ("total_radius", floatToJson r.totalRadius),
      ("logits_lo", Json.arr (r.lo.map floatToJson)),
      ("logits_hi", Json.arr (r.hi.map floatToJson)),
      ("time_ns", Lean.toJson r.timeNs) ]

/-- Sums every `Float` a box's two bounds (and the per-layer radii beside
it) hold, forcing the whole propagated result -- `Timing.lean`'s own reason:
an unread `let` is not demanded before the clock stops otherwise. -/
def forceBox {m : ℕ} (toD : 𝕋 → Float) (H : Interval (Vec 𝕋 m)) (radii : Array Float) : Float :=
  let ioSum := (Array.ofFn fun i : Fin m => toD (H.inf i) + toD (H.sup i)).foldl (· + ·) 0.0
  ioSum + radii.foldl (· + ·) 0.0


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Runs one image `reps` times, timing each with `IO.monoNanosNow` and
forcing the result through `forceBox`; returns the median of the `reps`
samples and the last propagation (every rep computes the same). -/
def aux_timeImage (instUnchecked : ExactDyadic → 𝕋) (toD : 𝕋 → Float)
    (overflows : Option (𝕋 → Bool)) (layers : List MnistAffine) (reps : ℕ) (img : MnistImage) :
    IO (ℕ × Interval (Vec 𝕋 (finalDim layers img.pixels.size)) × Array Float × Bool) := do
  let mut samples := #[]
  let mut last := none
  for _ in [0:reps] do
    let t0 ← IO.monoNanosNow
    -- `.materialise`: unmaterialised, the first layer's sum reads every pixel once per output row
    let X0 := (inputBox (𝕋 := 𝕋) instUnchecked img.pixels).materialise
    let (H, radii, over) := runReport instUnchecked toD overflows layers X0
    if (forceBox toD H radii).isNaN || over then
      IO.eprintln "nn-mnist: a bound is NaN -- likely overflow at this precision"
    else pure ()
    let t1 ← IO.monoNanosNow
    samples := samples.push (t1 - t0)
    last := some (H, radii, over)
  let (H, radii, over) := last.getD (runReport instUnchecked toD overflows layers
    (inputBox (𝕋 := 𝕋) instUnchecked img.pixels).materialise)
  pure (medianNanos samples, H, radii, over)

/-- One image's full record, plus its per-layer radii for `-layers.dat` --
`lo`/`hi` and the argmax read off the doubles, `certified` off `𝕋`'s own
bounds instead, through `ltStrict`. -/
def aux_runImage (instUnchecked : ExactDyadic → 𝕋) (toD : 𝕋 → Float)
    (overflows : Option (𝕋 → Bool)) (layers : List MnistAffine) (reps : ℕ) (img : MnistImage) :
    IO (ImageResult × Array Float) := do
  let (medianNs, H, radii, over) ← aux_timeImage instUnchecked toD overflows layers reps img
  let m := finalDim layers img.pixels.size
  let lo := Array.ofFn fun i : Fin m => toD (H.inf i)
  let hi := Array.ofFn fun i : Fin m => toD (H.sup i)
  let loT := Array.ofFn fun i : Fin m => H.inf i
  let hiT := Array.ofFn fun i : Fin m => H.sup i
  let predicted := argmaxFloat (Array.ofFn fun i : Fin m => (lo.getD i 0.0 + hi.getD i 0.0) / 2.0)
  let predLo := loT.getD predicted zero
  -- every other logit's upper bound strictly below the predicted class's lower bound, in range
  let certified := !over && Id.run do
    let mut ok := true
    for j in [0:m] do
      if j ≠ predicted then
        if !ltStrict (hiT.getD j zero) predLo then ok := false
    pure ok
  -- a box carries no separate generators/error box, so both radii coincide
  let radius := maxRadiusArr lo hi
  pure (⟨img.label, predicted, certified, radius, radius, lo, hi, medianNs, over⟩, radii)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `<out>/nn-mnist/<net>/<type>[-<format>]`, before the `.json`/`-layers.dat`
extension. -/
def mnistOutPath (outDir net ty format : String) : System.FilePath :=
  let label := if ty = "float" then ty else s!"{ty}-{format}"
  System.FilePath.mk outDir / "nn-mnist" / net / label

/-- Loads `--net`'s network and the first `--images` images, runs each
`--reps` times through `MnistNetwork.runReport`, and writes both output
files. `inst`/`toExact` are unused: nothing here needs either. -/
def runNnMnist (args : CliArgs) (_inst : String → ExactDyadic → Except String 𝕋)
    (instUnchecked : ExactDyadic → 𝕋) (toD : 𝕋 → Float) (format : String)
    (_toExact : Option (𝕋 → String)) (sig : ℕ) (nt : NumberType 𝕋 := {}) : IO Unit := do
  let netName := args.net.getD "small"
  let netPath ← match netFile netName with
    | .ok p => pure p
    | .error e => throw (IO.userError s!"nn-mnist: {e}")
  let netText ← IO.FS.readFile netPath
  let net ← match parseMnistNet netText with
    | .ok n => pure n
    | .error e => throw (IO.userError s!"nn-mnist: {netPath}: {e}")
  let dataText ← IO.FS.readFile dataFile
  let allImages ← match parseMnistData dataText with
    | .ok d => pure d
    | .error e => throw (IO.userError s!"nn-mnist: {dataFile}: {e}")
  let numImages := min (args.images.getD 100) allImages.size
  let images := allImages.extract 0 numImages
  let layers := net.layers.toList
  let reps := args.reps.getD 1
  -- read only, for `meta.weights_exact`; every precision is sound regardless
  let allExact := net.layers.all fun l =>
    l.W.all (·.all (fitsPrecision sig)) && l.b.all (fitsPrecision sig)
  -- one record and one layer-radii array per image
  let mut results : Array ImageResult := #[]
  let mut layerRadiiPerImage : Array (Array Float) := #[]
  for img in images do
    let (r, radii) ← aux_runImage instUnchecked toD nt.overflows layers reps img
    results := results.push r
    layerRadiiPerImage := layerRadiiPerImage.push radii
  let n := results.size
  let nF := Nat.toFloat (max n 1)
  let meanOf (f : ImageResult → Float) : Float := (results.foldl (fun acc r => acc + f r) 0.0) / nF
  let maxOf (f : ImageResult → Float) : Float := results.foldl (fun acc r => max acc (f r)) 0.0
  let certifiedFrac : Float := (Nat.toFloat (results.foldl
    (fun acc r => if r.certified then acc + 1 else acc) 0)) / nF
  let accuracy : Float := (Nat.toFloat (results.foldl
    (fun acc r => if r.predicted = r.label then acc + 1 else acc) 0)) / nF
  let times := results.map (·.timeNs)
  let medianTimeNs := medianNanos times
  -- per-layer aggregation: `L` layers, each image contributing one radius
  let numLayers := net.layers.size
  let layerMean : Array Float := Array.ofFn fun l : Fin numLayers =>
    (layerRadiiPerImage.foldl (fun acc row => acc + row.getD l.val 0.0) 0.0) / nF
  let layerMax : Array Float := Array.ofFn fun l : Fin numLayers =>
    layerRadiiPerImage.foldl (fun acc row => max acc (row.getD l.val 0.0)) 0.0
  let commit ← gitCommit
  let leanVer ← leanVersion
  let mach ← machineInfo
  -- `--type nearest` (CORA's own round-to-nearest) has no soundness guarantee at all
  let sound := args.ty ≠ "nearest"
  -- everything about the run that is not a per-image number
  let metaJ := Json.mkObj (
    [ ("experiment", Json.str "nn-mnist"),
      ("net", Json.str netName),
      ("type", Json.str args.ty),
      ("format", Json.str format),
      ("significand_bits", Lean.toJson sig),
      ("sound", Json.bool sound),
      ("label", Json.str (if sound then "sound" else "round-to-nearest (as in CORA), unverified")),
      ("weights_exact", Json.bool allExact),
      ("images", Lean.toJson n),
      ("reps", Lean.toJson reps),
      ("gitCommit", Json.str commit),
      ("leanVersion", Json.str leanVer),
      ("machine", Json.mkObj
        [ ("uname", Json.str mach.uname), ("cpu", Json.str mach.cpu),
          ("cores", Lean.toJson mach.cores) ]) ] ++ nt.metaFields)
  let overflowed := results.foldl (fun acc r => if r.overflow then acc + 1 else acc) 0
  -- `experiments/README.md`'s table; `certified_fraction` is a string, not a number, if `!sound`
  let summaryJ := Json.mkObj <|
    (if nt.overflows.isSome then [("overflowed_images", Lean.toJson overflowed)] else []) ++
    [ ("accuracy", floatToJson accuracy),
      ("certified_fraction", if sound then floatToJson certifiedFrac else Json.str "n/a (unsound)"),
      ("error_radius", Json.mkObj [("mean", floatToJson (meanOf (·.errorRadius))),
        ("max", floatToJson (maxOf (·.errorRadius)))]),
      ("total_radius", Json.mkObj [("mean", floatToJson (meanOf (·.totalRadius))),
        ("max", floatToJson (maxOf (·.totalRadius)))]),
      ("median_time_ns", Lean.toJson medianTimeNs) ]
  let layersJ := Json.arr (Array.ofFn fun l : Fin numLayers => Json.mkObj
    [ ("index", Lean.toJson l.val), ("mean_radius", floatToJson (layerMean.getD l.val 0.0)),
      ("max_radius", floatToJson (layerMax.getD l.val 0.0)) ])
  let doc := Json.mkObj
    [ ("meta", metaJ), ("summary", summaryJ), ("images", Json.arr (results.map ImageResult.json)),
      ("layers", layersJ) ]
  -- the JSON, then the pgfplots-ready per-layer table beside it
  let out := mnistOutPath args.outDir netName args.ty format
  match out.parent with
  | some dir => IO.FS.createDirAll dir
  | none => pure ()
  IO.FS.writeFile (out.toString ++ ".json") doc.pretty
  let datRows := (Array.ofFn fun l : Fin numLayers =>
    s!"{l.val} {floatToCsv (layerMean.getD l.val 0.0)} {floatToCsv (layerMax.getD l.val 0.0)}")
  IO.FS.writeFile (out.toString ++ "-layers.dat")
    ("# layer mean_radius max_radius\n" ++ String.intercalate "\n" datRows.toList ++ "\n")
  let certifiedStr := if sound then toString certifiedFrac else "n/a (unsound)"
  let tyStr := if nt.description = "" then args.ty else nt.description
  let overStr := if nt.overflows.isSome then s!", {overflowed} overflowed" else ""
  IO.println s!"nn-mnist: {netName} {tyStr}: {n} images, accuracy {accuracy}, certified \
    {certifiedStr}{overStr}, mean error radius {meanOf (·.errorRadius)}, max \
    {maxOf (·.errorRadius)}, median {medianTimeNs} ns/image"
  IO.println s!"nn-mnist: wrote {out}.json and {out}-layers.dat"

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
