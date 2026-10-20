import CORALean.Examples.Bench.FirstStepHead
import CORALean.Examples.Bench.FirstStepPrec
import CORALean.Examples.Bench.FirstStepRecord
import CORALean.Examples.Bench.FirstStepRun
import CORALean.Examples.Bench.Ieee
import CORALean.Examples.Bench.Config
import CORALean.Examples.Bench.FirstStepInput
import CORALean.Examples.Bench.Format
import CORALean.Examples.Bench.NearestUnsound.Instances
import CORALean.Examples.Bench.NearestUnsound.NearestDyadic
import CORALean.Examples.Bench.NearestUnsound.NearestFloat
import CORALean.Examples.Bench.NumberType
import CORALean.Examples.Bench.Rational
import CORALean.Global.Float.Instances.Dyadic.Instances
import CORALean.Global.Float.Instances.FixedPoint.Instances
import CORALean.Global.Float.Instances.IEEE.Instances

/-!
# `firststep`: the number types `bench` links

`firstStepBenchRecord` instantiates `FirstStepRecord.firstStepRecord` at the scalar a run's
`type` names -- `Dyadic p`, `IEEE fmt`, `FixedPoint f`, or round-to-nearest (`NearestFloat`,
or `NearestDyadic p`, unsound) -- with the same `inst` as `Registry.dispatch`'s, and `none` for
`flint`. `p` is `prec` if given, else `format` through `formatToPrec`, else `53`; `f` is
`digits`, else `4`.

## Inputs
* `cfg` – headline config
* `run` – first-step run description
* `dt` – step size as a string

## Output
* first-step record at the run's number type
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench

open CORALean CORALean.Float CORALean.Bench.NearestUnsound
open Lean (Json)


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `d` at `FixedPoint f`, exactly and off the grid: `m * 5^k / 10^k` for `d = m * 2^-k`, so
that `addDown`/`addUp` round it to `f` digits (`toFixedPointUnchecked` floors it instead). -/
def aux_fixedExact {f : ℕ} (d : ExactDyadic) : FixedPoint f :=
  if 0 ≤ d.exponent then ⟨d.mantissa * 2 ^ d.exponent.toNat, 0⟩
  else ⟨d.mantissa * 5 ^ (-d.exponent).toNat, (-d.exponent).toNat⟩


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One record, `none` for a run whose type this executable does not link. -/
def firstStepBenchRecord (cfg : HeadlineConfig) (run : FirstStepRun) (dt : String) :
    Option Json :=
  -- one instantiation per `type`, each with the `inst` `Registry.dispatch` gives it
  match run.ty with
  | "dyadic" =>
    let p := run.sigBits
    let nt : NumberType (Dyadic p) := { description := dyadicDescription (precToFormat p) p }
    some (firstStepRecord cfg (firstStepHead "dyadic" s!"p{p}" p nt)
      (fun field d => d.toDyadicP field p) ExactDyadic.toDyadicPUnchecked nt dt)
  | "ieee" =>
    match ieeeFormat (run.format.getD "binary64") with
    | .error e => some (Json.mkObj [("status", Json.str "none"), ("reason", Json.str e)])
    | .ok fmt =>
      let label := run.format.getD "binary64"
      let nt := ieeeNumberType label fmt
      some (firstStepRecord cfg (firstStepHead "ieee" label fmt.p nt)
        (fun field d => d.toIEEE field fmt) ExactDyadic.toIEEEUnchecked nt dt)
  | "fixed" =>
    -- decimal digits, `FixedPoint f`: `1/16` needs `f ≥ 4`, `1/64` `f ≥ 6`
    let f := run.digits.getD 4
    let nt : NumberType (FixedPoint f) :=
      { description := s!"decimal fixed point, {f} fractional digits" }
    some (firstStepRecord cfg (firstStepHead "fixed" s!"decimal{f}" f nt)
      (fun field d => d.toFixedPoint field f) aux_fixedExact nt dt)
  | "nearest" =>
    -- the unsound baseline: native `Float`, or `Dyadic p` rounded to nearest
    match run.prec, run.format with
    | none, none | none, some "binary64" =>
      let nt : NumberType NearestFloat :=
        { description := "round-to-nearest binary64 (native Float, unsound)"
          overflows := some fun x => x.val.isNaN || x.val.isInf }
      some (firstStepRecord cfg (firstStepHead "nearest" "binary64" 53 nt)
        (fun field d => (ExactDyadic.toFloat field d).map (⟨·⟩))
        (fun d => ⟨ExactDyadic.toFloatUnchecked d⟩) nt dt)
    | _, _ =>
      let p := run.sigBits
      let nt : NumberType (NearestDyadic p) :=
        { description := s!"round-to-nearest {dyadicDescription (precToFormat p) p}, unsound" }
      some (firstStepRecord cfg (firstStepHead "nearest" s!"p{p}" p nt)
        (fun field d => (d.toDyadicP field p).map (⟨·⟩))
        (fun d => ⟨ExactDyadic.toDyadicPUnchecked d⟩) nt dt)
  | _ => none

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
