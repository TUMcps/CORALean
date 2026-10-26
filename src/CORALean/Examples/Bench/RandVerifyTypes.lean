import CORALean.Examples.Bench.FirstStepHead
import CORALean.Examples.Bench.Format
import CORALean.Examples.Bench.Ieee
import CORALean.Examples.Bench.NearestUnsound.Instances
import CORALean.Examples.Bench.NearestUnsound.NearestDyadic
import CORALean.Examples.Bench.NearestUnsound.NearestFloat
import CORALean.Examples.Bench.NumberType
import CORALean.Examples.Bench.RandVerifyInstance
import CORALean.Examples.Bench.RandVerifyJob
import CORALean.Examples.Bench.Rational
import CORALean.Global.Float.Instances.Binary64.Instances
import CORALean.Global.Float.Instances.Dyadic.Instances
import CORALean.Global.Float.Instances.IEEE.Instances
import CORALean.Examples.Bench.RandVerifyLabel
import CORALean.Examples.Bench.RandVerifyRecord

/-!
# `randverify`: the number types `bench` links

`randVerifyBenchRecord` instantiates `randVerifyRecords` at the scalar a label names (see
`randTypeKind`): `Dyadic p`, `IEEE fmt`, the hardware `Float`, and round-to-nearest (`NearestFloat`
or `NearestDyadic p`, unsound), with the same readers `firstStepBenchRecord` uses. `none` for
`flint<p>`, which only `bench-flint` links, and for a label that is no type.

## Inputs
* `label` – number type label
* `J` – job
* `insts` – instances sharing the system

## Output
* records at the labelled type, none if not linked
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       01-October-2026
-- Last update:   01-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench

open CORALean CORALean.Float CORALean.Bench.NearestUnsound
open Lean (Json)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The run for one label, `none` where this executable has no such type. -/
def randVerifyBenchRecord (label : String) (J : RandJob) (insts : Array RandInstance) :
    Option (IO (Array Json)) :=
  match randTypeKind label with
  | some ("dyadic", some p) =>
    let nt : NumberType (Dyadic p) := { description := dyadicDescription (precToFormat p) p }
    some (randVerifyRecords (firstStepHead "dyadic" s!"p{p}" p nt) nt
      (fun field d => d.toDyadicP field p) ExactDyadic.toDyadicPUnchecked J insts)
  | some ("ieee", _) =>
    match ieeeFormat label with
    | .error _ => none
    | .ok fmt =>
      let nt := ieeeNumberType label fmt
      some (randVerifyRecords (firstStepHead "ieee" label fmt.p nt) nt
        (fun field d => d.toIEEE field fmt) ExactDyadic.toIEEEUnchecked J insts)
  | some ("hardware", _) =>
    let nt : NumberType Float :=
      { description := "hardware binary64 (native Float, trusted, NaN outside the normal range)"
        overflows := some fun x => x.isNaN || x.isInf }
    some (randVerifyRecords (firstStepHead "hardware" "binary64" 53 nt) nt
      ExactDyadic.toFloat ExactDyadic.toFloatUnchecked J insts)
  | some ("nearest", none) =>
    -- the unsound baseline: native `Float` rounded to nearest
    let nt : NumberType NearestFloat :=
      { description := "round-to-nearest binary64 (native Float, unsound)"
        overflows := some fun x => x.val.isNaN || x.val.isInf }
    some (randVerifyRecords (firstStepHead "nearest" "binary64" 53 nt) nt
      (fun field d => (ExactDyadic.toFloat field d).map (⟨·⟩))
      (fun d => ⟨ExactDyadic.toFloatUnchecked d⟩) J insts)
  | some ("nearest", some p) =>
    let nt : NumberType (NearestDyadic p) :=
      { description := s!"round-to-nearest {dyadicDescription (precToFormat p) p}, unsound" }
    some (randVerifyRecords (firstStepHead "nearest" s!"p{p}" p nt) nt
      (fun field d => (d.toDyadicP field p).map (⟨·⟩))
      (fun d => ⟨ExactDyadic.toDyadicPUnchecked d⟩) J insts)
  | _ => none

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
