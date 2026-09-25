import CORALean.Examples.Bench.GitInfo
import CORALean.Examples.Bench.Timing
import Lean.Data.Json

/-!
# Writing a run out: one JSON file, one CSV

The JSON schema is `meta` (experiment, scheme, type/format/significand_bits,
the config echoed back, the git commit and machine the run ran on, timings)
beside `sets`, one record per step with its center, generators and error box.
`--exact` adds an `"exact"` string `"m*2^e"` beside every scalar's nearest
double -- `toExact none` is the default, `toExact (some f)` what `--exact`
switches on. The CSV holds what a pgfplots figure actually reads: the interval
hull's width per dimension and the error box's radius, derived once here so
`experiments/plot/` never has to recompute them from `G`.

`format`/`sig`, threaded through `metaJson` and `writeRun`, are the IEEE-shaped
label and significand width `Format.lean` maps to and from -- `"binary64"`/`53`
for `float` always, whichever `Registry.resolvedPrec` picked for `dyadic`.
-/

-- Authors:       Tobias Ladner
-- Written:       25-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench

open CORALean CORALean.Float
open Lean (Json)

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]

/-- A scalar as JSON: its nearest double always, and `"m*2^e"` beside it when
`toExact` is given -- the one place `--exact` changes the output. -/
def scalarJson (toD : 𝕋 → Float) (toExact : Option (𝕋 → String)) (x : 𝕋) : Json :=
  match toExact with
  | none => Lean.toJson (toD x)
  | some f => Json.mkObj [("double", Lean.toJson (toD x)), ("exact", Json.str (f x))]

/-- One `sets` record: `k`, the time interval it covers (equal endpoints for a
time-point set, as `dtdemo`'s discrete-time steps are), and the zonotope's own
fields. -/
def stepJson (toD : 𝕋 → Float) (toExact : Option (𝕋 → String)) (k : ℕ) (t0 t1 : Float)
    (Z : Zonotope 𝕋 2) : Json :=
  let sj := scalarJson toD toExact
  Json.mkObj
    [ ("k", Lean.toJson k),
      ("t0", Lean.toJson t0),
      ("t1", Lean.toJson t1),
      ("c", Json.arr (Array.ofFn fun i => sj (Z.c i))),
      ("G", Json.arr (Array.ofFn fun i => Json.arr (Array.ofFn fun j => sj (Z.G i j)))),
      ("E", Json.mkObj
        [ ("inf", Json.arr (Array.ofFn fun i => sj (Z.E.inf i))),
          ("sup", Json.arr (Array.ofFn fun i => sj (Z.E.sup i))) ]) ]

/-- `meta`: everything about the run that is not a per-step number. `configJ`
is the config file's own parsed `Json`, echoed back verbatim rather than
re-serialised, so it can never drift from what was read. -/
def metaJson (experiment scheme ty format : String) (sig : ℕ) (configJ : Json) (eta : ℕ)
    (commit leanVer : String) (mach : MachineInfo) (samples : Array Nat) (medianNs : Nat) :
    IO Json := do
  pure (Json.mkObj
    [ ("experiment", Json.str experiment),
      ("scheme", Json.str scheme),
      ("type", Json.str ty),
      ("format", Json.str format),
      ("significand_bits", Lean.toJson sig),
      ("config", configJ),
      ("eta", Lean.toJson eta),
      ("gitCommit", Json.str commit),
      ("leanVersion", Json.str leanVer),
      ("machine", Json.mkObj
        [ ("uname", Json.str mach.uname), ("cpu", Json.str mach.cpu),
          ("cores", Lean.toJson mach.cores) ]),
      ("timingsNs", Json.arr (samples.map Lean.toJson)),
      ("medianNs", Lean.toJson medianNs) ])

/-- One row of the CSV per step: `k`, `t`, the nominal hull's width per
dimension (`2 * sum |G_ij|`, CORA's own interval-hull formula), and the error
box's radius per dimension (`sup - inf`, unsigned by construction). -/
def csvRow (toD : 𝕋 → Float) (k : ℕ) (t : Float) (Z : Zonotope 𝕋 2) : String :=
  let width (i : Fin 2) : Float :=
    2.0 * (Array.ofFn fun j => (toD (Z.G i j)).abs).foldl (· + ·) 0.0
  let radius (i : Fin 2) : Float := toD (Z.E.sup i) - toD (Z.E.inf i)
  s!"{k},{t},{width 0},{width 1},{radius 0},{radius 1}"

def csvHeader : String := "k,t,width0,width1,Eradius0,Eradius1"


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Writes `<out>.json` and `<out>.csv` for one run, built from `steps` (one
`Zonotope` per `k`, at time `t k`). Creates `out`'s parent directory first. -/
def writeRun (out : System.FilePath) (experiment scheme ty format : String) (sig : ℕ)
    (configJ : Json) (eta : ℕ) (samples : Array Nat) (medianNs : Nat) (toD : 𝕋 → Float)
    (toExact : Option (𝕋 → String)) (dtFloat : Float) (steps : Array (Zonotope 𝕋 2)) :
    IO Unit := do
  -- Creates `out`'s directory first, so a fresh `<config>/<exp>/` need not exist.
  match out.parent with
  | some dir => IO.FS.createDirAll dir
  | none => pure ()
  let commit ← gitCommit
  let leanVer ← leanVersion
  let mach ← machineInfo
  let metaJ ← metaJson experiment scheme ty format sig configJ eta commit leanVer mach samples
    medianNs
  let sets := Json.arr (steps.mapIdx fun k Z =>
    let t := dtFloat * Nat.toFloat k
    stepJson toD toExact k t t Z)
  let doc := Json.mkObj [("meta", metaJ), ("sets", sets)]
  IO.FS.writeFile (out.toString ++ ".json") doc.pretty
  let rows := steps.mapIdx fun k Z => csvRow toD k (dtFloat * Nat.toFloat k) Z
  let csv := csvHeader ++ "\n" ++ String.intercalate "\n" rows.toList ++ "\n"
  IO.FS.writeFile (out.toString ++ ".csv") csv

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
