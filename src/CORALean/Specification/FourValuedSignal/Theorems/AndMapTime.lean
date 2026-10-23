module

public import CORALean.Specification.FourValuedSignal.Operations.And
public import CORALean.Specification.FourValuedSignal.Theorems.ToKleeneSignalMapTime
public import CORALean.Specification.KleeneSignal.Theorems.ToBoolSignalMapTime
public import CORALean.Specification.PointSegmentSignal.Theorems.CombineMapTime
public import CORALean.Specification.KleeneSignal.Theorems.CombineMapTime
public import CORALean.Specification.KleeneSignal.Theorems.ToBoolSignalOptionMapTime

@[expose] public section

/-!
# The four-valued conjunction at a float time type, read as reals

Over a float scalar `𝕋` the refinements, their Kleene conjunctions and the inconclusive part are all
computed exactly, so the float conjunction read as reals is the one of the inputs read as reals, and
both are undefined together.

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

theorem FourValuedSignal.and_mapTime (sigs : ι → FourValuedSignal 𝕋) : -- --- CONCL ---
    (FourValuedSignal.and_ sigs).map (·.mapTime toReal) =
      FourValuedSignal.and_ (fun k => (sigs k).mapTime toReal) := by -- --- PROOF ---
  -- the refinements and their conjunctions read as reals, then their range
  have h2 : ∀ a b : KleeneSignal 𝕋,
      ![a.mapTime toReal, b.mapTime toReal] = (fun j => (![a, b] j).mapTime toReal) :=
    fun a b => funext fun j => match j with | 0 => rfl | 1 => rfl
  have h2' : ∀ a b : PointSegmentSignal 𝕋,
      (fun j => (![a, b] j).mapTime toReal) = ![a.mapTime toReal, b.mapTime toReal] :=
    fun a b => funext fun j => match j with | 0 => rfl | 1 => rfl
  -- the Kleene and_ of the refinements, read as reals
  have hk : ∀ s : ι → KleeneSignal 𝕋, (KleeneSignal.and_ s).mapTime toReal =
      KleeneSignal.and_ (fun k => (s k).mapTime toReal) := fun s => by
    simp only [KleeneSignal.and_, KleeneSignal.mapTime, PointSegmentSignal.combine_mapTime, h2',
      KleeneSignal.toBoolSignal_mapTime]
  simp only [FourValuedSignal.and_, ← FourValuedSignal.toKleeneSignal_mapTime, ← hk, h2,
    ← KleeneSignal.combine_mapTime, KleeneSignal.toBoolSignal?_mapTime, Option.map_map]
  rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
