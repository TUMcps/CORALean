module

public import CORALean.Specification.Kleene.Kleene
public import CORALean.Specification.KleeneSignal.Operations.Basic
public import CORALean.Specification.KleeneSignal.Operations.ToBoolSignal
public import CORALean.Specification.PointSegmentSignal.Operations.FindIntervals

@[expose] public section

/-!
# The intervals where a three-valued signal has a value

`intervals = findIntervals(obj,match)` of `kleeneSignal.m`: the maximal intervals where the signal
is `match` (by default `True`). The unknown intervals are those of `isUnknown`; the true ones are
found after mapping unknown to false, and the false ones, with the condition `~x`, after mapping
unknown to true.

## Inputs
* `s` – three-valued signal
* `match_` – value to find

## Output
* the maximal intervals where the signal has that value
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋] [Float.ExactLe 𝕋]
    [TimeOrder 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `intervals = findIntervals(obj,match)`. -/
def KleeneSignal.findIntervals (s : KleeneSignal 𝕋) (match_ : Kleene := Kleene.tt) :
    List (STLInterval 𝕋) :=
  match match_ with
  | Kleene.uu => s.isUnknown.findIntervals
  | Kleene.tt => (s.toBoolSignal false).findIntervals
  | Kleene.ff => (s.toBoolSignal true).findIntervals (fun x => !x)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
