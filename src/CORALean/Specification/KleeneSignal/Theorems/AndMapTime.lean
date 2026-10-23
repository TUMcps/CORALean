module

public import CORALean.Specification.KleeneSignal.Operations.And
public import CORALean.Specification.KleeneSignal.Theorems.ToBoolSignalMapTime
public import CORALean.Specification.PointSegmentSignal.Theorems.CombineMapTime

@[expose] public section

/-!
# The Kleene conjunction at a float time type, read as reals

Over a float scalar `𝕋` the refinements are made and combined exactly
(`KleeneSignal.toBoolSignal_mapTime`, `PointSegmentSignal.combine_mapTime`), so the float
conjunction read as reals is the one of the inputs read as reals.

## Inputs
* `sigs` – input signals

## Hypotheses
* none

## Conclusion
* it commutes with reading the time points as reals
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋] {ι : Type} [FinEnum ι]


-- =======================================  MAIN THEOREM  ======================================= --

theorem KleeneSignal.and_mapTime (sigs : ι → KleeneSignal 𝕋) : -- --- CONCL ---
    (KleeneSignal.and_ sigs).mapTime toReal =
      KleeneSignal.and_ (fun k => (sigs k).mapTime toReal) := by -- --- PROOF ---
  -- the two refinements read as reals, then their range
  have h2 : ∀ a b : PointSegmentSignal 𝕋,
      (fun j => (![a, b] j).mapTime toReal) = ![a.mapTime toReal, b.mapTime toReal] :=
    fun a b => funext fun j => match j with | 0 => rfl | 1 => rfl
  simp only [KleeneSignal.and_, KleeneSignal.mapTime, PointSegmentSignal.combine_mapTime, h2,
    KleeneSignal.toBoolSignal_mapTime]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
