module

public import CORALean.Specification.FourValuedSignal.Operations.Basic
public import CORALean.Specification.PointSegmentSignal.Theorems.CombineMapTime
public import CORALean.Specification.TentativeKleeneSignal.Operations.Basic
public import CORALean.Specification.TentativeKleeneSignal.Operations.ToFourValued

@[expose] public section

/-!
# A tentative signal made four-valued at a float time type, read as reals

Over a float scalar `𝕋` the parts are combined exactly (`PointSegmentSignal.combine_mapTime`), so
the float four-valued signal read as reals is the one made from the tentative signal read as
reals.

## Inputs
* `s` – signal

## Hypotheses
* none

## Conclusion
* making the signal four-valued commutes with reading the time points as reals
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem TentativeKleeneSignal.toFourValued_mapTime (s : TentativeKleeneSignal 𝕋) : -- --- CONCL ---
    s.toFourValued.mapTime toReal = (s.mapTime toReal).toFourValued := by -- --- PROOF ---
  -- the two parts read as reals, then their combinations
  have h2 : ∀ a b : PointSegmentSignal 𝕋,
      ![a.mapTime toReal, b.mapTime toReal] = (fun j => (![a, b] j).mapTime toReal) :=
    fun a b => funext fun j => match j with | 0 => rfl | 1 => rfl
  simp only [TentativeKleeneSignal.toFourValued, TentativeKleeneSignal.mapTime, h2,
    ← PointSegmentSignal.combine_mapTime]
  rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
