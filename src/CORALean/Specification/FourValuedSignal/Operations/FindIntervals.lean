module

public import CORALean.Specification.FourValued.FourValued
public import CORALean.Specification.FourValuedSignal.Operations.ToKleeneSignal
public import CORALean.Specification.KleeneSignal.Operations.FindIntervals
public import CORALean.Specification.PointSegmentSignal.Operations.FindIntervals

@[expose] public section

/-!
# The intervals where a four-valued signal has a value

`intervals = findIntervals(obj,match)` of `fourValuedSignal.m`: the maximal intervals where the
signal is `match` (by default `True`). The inconclusive intervals are those of `isInconclusive`; the
others are found on the Kleene refinement that maps inconclusive to `False` for `True`, and to
`True` for `False` and `Unknown`.

## Inputs
* `s` – four-valued signal
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
def FourValuedSignal.findIntervals (s : FourValuedSignal 𝕋)
    (match_ : FourValued := FourValued.tt) : List (STLInterval 𝕋) :=
  match match_ with
  | FourValued.ii => s.isInconclusive.findIntervals
  | FourValued.tt => (s.toKleeneSignal Kleene.ff).findIntervals Kleene.tt
  | FourValued.ff => (s.toKleeneSignal Kleene.tt).findIntervals Kleene.ff
  | FourValued.uu => (s.toKleeneSignal Kleene.tt).findIntervals Kleene.uu

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
