import CORALean.Examples.Bench.FirstStepHead
import CORALean.Examples.Bench.Format
import CORALean.Examples.Bench.Ieee
import CORALean.Examples.Bench.NearestUnsound.API
import CORALean.Examples.Bench.RandVerifyLabel
import CORALean.Examples.Bench.RandVerifyRecord
import CORALean.Global.Float.Instances.Binary64.API
import CORALean.Global.Float.Instances.Dyadic.API
import CORALean.Global.Float.Instances.IEEE.API

/-!
# `randverify`: the number types `bench` links

`randVerifyBenchRecord` instantiates `randVerifyRecord` at the scalar a label names (see
`randTypeKind`): `Dyadic p`, `IEEE fmt`, the hardware `Float`, and round-to-nearest (`NearestFloat`
or `NearestDyadic p`, unsound), with the same readers `firstStepBenchRecord` uses. `none` for
`flint<p>`, which only `bench-flint` links, and for a label that is no type.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench

open CORALean CORALean.Float CORALean.Bench.NearestUnsound
open Lean (Json)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The run for one label, `none` where this executable has no such type. -/
def randVerifyBenchRecord (label : String) (J : RandJob) : Option (IO Json) :=
  match randTypeKind label with
  | some ("dyadic", some p) =>
    let nt : NumberType (Dyadic p) := { description := dyadicDescription (precToFormat p) p }
    some (randVerifyRecord (firstStepHead "dyadic" s!"p{p}" p nt) nt
      (fun field d => d.toDyadicP field p) ExactDyadic.toDyadicPUnchecked J)
  | some ("ieee", _) =>
    match ieeeFormat label with
    | .error _ => none
    | .ok fmt =>
      let nt := ieeeNumberType label fmt
      some (randVerifyRecord (firstStepHead "ieee" label fmt.p nt) nt
        (fun field d => d.toIEEE field fmt) ExactDyadic.toIEEEUnchecked J)
  | some ("float", _) =>
    let nt : NumberType Float :=
      { description := "hardware binary64 (native Float, trusted, NaN outside the normal range)"
        overflows := some fun x => x.isNaN || x.isInf }
    some (randVerifyRecord (firstStepHead "float" "binary64" 53 nt) nt
      ExactDyadic.toFloat ExactDyadic.toFloatUnchecked J)
  | some ("nearest", none) =>
    -- the unsound baseline: native `Float` rounded to nearest
    let nt : NumberType NearestFloat :=
      { description := "round-to-nearest binary64 (native Float, unsound)"
        overflows := some fun x => x.val.isNaN || x.val.isInf }
    some (randVerifyRecord (firstStepHead "nearest" "binary64" 53 nt) nt
      (fun field d => (ExactDyadic.toFloat field d).map (⟨·⟩))
      (fun d => ⟨ExactDyadic.toFloatUnchecked d⟩) J)
  | some ("nearest", some p) =>
    let nt : NumberType (NearestDyadic p) :=
      { description := s!"round-to-nearest {dyadicDescription (precToFormat p) p}, unsound" }
    some (randVerifyRecord (firstStepHead "nearest" s!"p{p}" p nt) nt
      (fun field d => (d.toDyadicP field p).map (⟨·⟩))
      (fun d => ⟨ExactDyadic.toDyadicPUnchecked d⟩) J)
  | _ => none

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
