module

public import CORALean.Specification.FourValuedSignal.Operations.ToKleeneSignal
public import CORALean.Specification.KleeneSignal.Theorems.SetMapTime
public import CORALean.Specification.PointSegmentSignal.Theorems.FindIntervalsMapTime

@[expose] public section

/-!
# A four-valued signal made Kleene at a float time type, read as reals

Over a float scalar `𝕋` the inconclusive intervals are found and set exactly
(`PointSegmentSignal.findIntervals_mapTime`, `KleeneSignal.set_mapTime`), so the float Kleene
signal read as reals is the one made from the four-valued signal read as reals.

## Inputs
* `s` – signal
* `mapInconclusiveTo` – value for inconclusive times

## Hypotheses
* none

## Conclusion
* making the signal Kleene commutes with reading the time points as reals
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

theorem FourValuedSignal.toKleeneSignal_mapTime (s : FourValuedSignal 𝕋)
    (mapInconclusiveTo : Kleene) : -- --- CONCL ---
    (s.toKleeneSignal mapInconclusiveTo).mapTime toReal =
      (s.mapTime toReal).toKleeneSignal mapInconclusiveTo := by -- --- PROOF ---
  -- the inconclusive intervals of the signal read as reals are the float ones read as reals
  unfold FourValuedSignal.toKleeneSignal
  simp only [FourValuedSignal.mapTime, ← PointSegmentSignal.findIntervals_mapTime]
  generalize s.isInconclusive.findIntervals id = L
  generalize s.signal = sig
  -- and each is set alike
  induction L generalizing sig with
  | nil => rfl
  | cons I L ih => simp only [List.foldl_cons, List.map_cons, ih, KleeneSignal.set_mapTime]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
