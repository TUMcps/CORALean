module

public import CORALean.Specification.KleeneSignal.Operations.Basic
public import CORALean.Specification.KleeneSignal.Operations.ToBoolSignal
public import CORALean.Specification.PointSegmentSignal.Theorems.FindIntervalsMapTime
public import CORALean.Specification.PointSegmentSignal.Theorems.SetMapTime

@[expose] public section

/-!
# A Kleene signal made Boolean at a float time type, read as reals

Over a float scalar `𝕋` the unknown intervals are found and set exactly
(`PointSegmentSignal.findIntervals_mapTime`, `PointSegmentSignal.set_mapTime`), so the float
Boolean signal read as reals is the one made from the Kleene signal read as reals.

## Inputs
* `s` – signal
* `mapUnknownTo` – value for unknown times

## Hypotheses
* none

## Conclusion
* making the signal Boolean commutes with reading the time points as reals
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

theorem KleeneSignal.toBoolSignal_mapTime (s : KleeneSignal 𝕋)
    (mapUnknownTo : Bool) : -- --- CONCL ---
    (s.toBoolSignal mapUnknownTo).mapTime toReal =
      (s.mapTime toReal).toBoolSignal mapUnknownTo := by -- --- PROOF ---
  -- the unknown intervals of the signal read as reals are the float ones read as reals
  unfold KleeneSignal.toBoolSignal
  simp only [KleeneSignal.mapTime, ← PointSegmentSignal.findIntervals_mapTime]
  generalize s.isUnknown.findIntervals id = L
  generalize s.signal = sig
  -- and each is set alike
  induction L generalizing sig with
  | nil => rfl
  | cons I L ih => simp only [List.foldl_cons, List.map_cons, ih, PointSegmentSignal.set_mapTime]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
