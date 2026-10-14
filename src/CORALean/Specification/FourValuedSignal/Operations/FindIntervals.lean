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
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `intervals = findIntervals(obj,match)`. -/
noncomputable def FourValuedSignal.findIntervals (s : FourValuedSignal ℝ)
    (match_ : FourValued := FourValued.tt) : List STLInterval :=
  match match_ with
  | FourValued.ii => s.isInconclusive.findIntervals
  | FourValued.tt => (s.toKleeneSignal Kleene.ff).findIntervals Kleene.tt
  | FourValued.ff => (s.toKleeneSignal Kleene.tt).findIntervals Kleene.ff
  | FourValued.uu => (s.toKleeneSignal Kleene.tt).findIntervals Kleene.uu

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
