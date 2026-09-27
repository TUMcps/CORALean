import CORALean.Examples.Bench.FloatPrint
import CORALean.Examples.Bench.GitInfo
import CORALean.Examples.Bench.Summary
import CORALean.Examples.Bench.Timing
import Lean.Data.Json

/-!
# Writing a run out: one JSON file, one CSV

`writeRun` (`dtdemo`): `meta` beside `sets`, one record per step. `writeRunTiTp`
(`headline-a`/`headline-b`/`exp2-timepoint`): `meta` beside two arrays,
`sets_ti` (`t0 < t1`) and `sets_tp` (`t0 = t1`), either empty where a scheme has
none, plus `meta.summary.ti`/`.tp` (`Summary.lean`) and the run's own
`eta`/`rho`/`N`/`dt`. `writeRunNone` is the `"status": "none"` case: the
algorithm returned `none`, so only why is written.

Every "nearest double", JSON or CSV, is `floatToJson`/`floatToCsv`'s
round-trip 17-digit decimal (`FloatPrint.lean`), not `Float.toString`'s six.
`--exact` adds `"m*2^e"` beside it. The CSV holds what a pgfplots figure
actually reads: the interval hull's width per dimension and the error box's
radius, derived once here so `experiments/plot/` never recomputes them from
`G`. `format`/`sig` are the IEEE-shaped label and significand width
`Format.lean` maps to and from.
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

/-- A scalar as JSON: its nearest double always (round-trip, `floatToJson`),
and `"m*2^e"` beside it when `toExact` is given -- the one place `--exact`
changes the output. -/
def scalarJson (toD : 𝕋 → Float) (toExact : Option (𝕋 → String)) (x : 𝕋) : Json :=
  match toExact with
  | none => floatToJson (toD x)
  | some f => Json.mkObj [("double", floatToJson (toD x)), ("exact", Json.str (f x))]

/-- One `sets`/`sets_ti`/`sets_tp` record: `k`, the time interval it covers
(equal endpoints for a time-point set), and the zonotope's own fields. -/
def stepJson (toD : 𝕋 → Float) (toExact : Option (𝕋 → String)) (k : ℕ) (t0 t1 : Float)
    (Z : Zonotope 𝕋 2) : Json :=
  let sj := scalarJson toD toExact
  Json.mkObj
    [ ("k", Lean.toJson k),
      ("t0", floatToJson t0),
      ("t1", floatToJson t1),
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
  let f := floatToCsv
  s!"{k},{f t},{f (width 0)},{f (width 1)},{f (radius 0)},{f (radius 1)}"

def csvHeader : String := "k,t,width0,width1,Eradius0,Eradius1"

/-- One `sets_ti`/`sets_tp` CSV row: `csvRow`'s own columns, `set` (`"ti"` or
`"tp"`) ahead of `k` so both arrays share one file. -/
def csvRowTagged (toD : 𝕋 → Float) (tag : String) (k : ℕ) (t : Float) (Z : Zonotope 𝕋 2) :
    String :=
  s!"{tag},{csvRow toD k t Z}"

def csvHeaderTagged : String := "set," ++ csvHeader


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

/-- `meta` for `headline-a`/`headline-b`/`exp2-timepoint`: `metaJson`'s fields,
plus `rho`, `N`, `dt` (the run's own, not just the config's) and `summary`. -/
def metaJsonRun (experiment scheme ty format : String) (sig : ℕ) (configJ : Json) (eta rho N : ℕ)
    (dtFloat : Float) (commit leanVer : String) (mach : MachineInfo) (samples : Array Nat)
    (medianNs : Nat) (summaryTi summaryTp : Json) : Json :=
  Json.mkObj
    [ ("status", Json.str "ok"),
      ("experiment", Json.str experiment),
      ("scheme", Json.str scheme),
      ("type", Json.str ty),
      ("format", Json.str format),
      ("significand_bits", Lean.toJson sig),
      ("config", configJ),
      -- the run's own tuning, not just the config's requested `eta`
      ("eta", Lean.toJson eta),
      ("rho", Lean.toJson rho),
      ("N", Lean.toJson N),
      ("dt", floatToJson dtFloat),
      ("gitCommit", Json.str commit),
      ("leanVersion", Json.str leanVer),
      ("machine", Json.mkObj
        [ ("uname", Json.str mach.uname), ("cpu", Json.str mach.cpu),
          ("cores", Lean.toJson mach.cores) ]),
      ("timingsNs", Json.arr (samples.map Lean.toJson)),
      ("medianNs", Lean.toJson medianNs),
      -- `Summary.summaryJson`'s object, one per array -- see that file for the fields
      ("summary", Json.mkObj [("ti", summaryTi), ("tp", summaryTp)]) ]

/-- Writes `<out>.json` (`meta`, `sets_ti`, `sets_tp`) and `<out>.csv` (both
arrays, tagged) for `headline-a`/`headline-b`/`exp2-timepoint` -- either array
may be empty, the scheme that has none of one kind. -/
def writeRunTiTp (out : System.FilePath) (experiment scheme ty format : String) (sig : ℕ)
    (configJ : Json) (eta rho N : ℕ) (samples : Array Nat) (medianNs : Nat) (toD : 𝕋 → Float)
    (toExact : Option (𝕋 → String)) (dtFloat : Float) (ti tp : Array (Zonotope 𝕋 2)) :
    IO Unit := do
  match out.parent with
  | some dir => IO.FS.createDirAll dir
  | none => pure ()
  let commit ← gitCommit
  let leanVer ← leanVersion
  let mach ← machineInfo
  -- `sets_ti`'s window `k` covers `[k Δt, (k+1) Δt]`; `sets_tp`'s covers `[k Δt, k Δt]`
  let setsTi := Json.arr (ti.mapIdx fun k Z =>
    stepJson toD toExact k (dtFloat * Nat.toFloat k) (dtFloat * Nat.toFloat (k + 1)) Z)
  let setsTp := Json.arr (tp.mapIdx fun k Z =>
    let t := dtFloat * Nat.toFloat k
    stepJson toD toExact k t t Z)
  let metaJ := metaJsonRun experiment scheme ty format sig configJ eta rho N dtFloat commit
    leanVer mach samples medianNs (summaryJson toD ti) (summaryJson toD tp)
  let doc := Json.mkObj [("meta", metaJ), ("sets_ti", setsTi), ("sets_tp", setsTp)]
  IO.FS.writeFile (out.toString ++ ".json") doc.pretty
  let rowsTi := ti.mapIdx fun k Z => csvRowTagged toD "ti" k (dtFloat * Nat.toFloat k) Z
  let rowsTp := tp.mapIdx fun k Z => csvRowTagged toD "tp" k (dtFloat * Nat.toFloat k) Z
  let csv := csvHeaderTagged ++ "\n" ++
    String.intercalate "\n" (rowsTi ++ rowsTp).toList ++ "\n"
  IO.FS.writeFile (out.toString ++ ".csv") csv

/-- Writes `<out>.json` alone, `{"status": "none", "reason": ...}` beside the
same identifying fields `writeRunTiTp` carries -- the algorithm returned
`none`; there is no `sets_ti`/`sets_tp`, only why, and no CSV. -/
def writeRunNone (out : System.FilePath) (experiment scheme ty format : String) (sig : ℕ)
    (configJ : Json) (reason : String) : IO Unit := do
  match out.parent with
  | some dir => IO.FS.createDirAll dir
  | none => pure ()
  let doc := Json.mkObj
    [ ("status", Json.str "none"),
      ("experiment", Json.str experiment),
      ("scheme", Json.str scheme),
      ("type", Json.str ty),
      ("format", Json.str format),
      ("significand_bits", Lean.toJson sig),
      ("config", configJ),
      ("reason", Json.str reason) ]
  IO.FS.writeFile (out.toString ++ ".json") doc.pretty

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
