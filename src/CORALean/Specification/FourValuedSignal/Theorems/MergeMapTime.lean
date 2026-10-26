module

public import CORALean.Specification.FourValuedSignal.Operations.Merge
public import CORALean.Specification.FourValuedSignal.Theorems.FindIntervalsMapTime
public import CORALean.Specification.FourValuedSignal.Theorems.SetMapTime

@[expose] public section

/-!
# Merging four-valued signals at a float time type, read as reals

Over a float scalar `𝕋` the intervals of `other` are found and set on `obj` exactly, so the
float merge read as reals is the merge of the two signals read as reals.

## Inputs
* `obj` – signal merged into
* `other` – signal merged

## Hypotheses
* none

## Conclusion
* merging commutes with reading the time points as reals
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Setting a value on a list of intervals commutes with reading the time points as reals. -/
private theorem FourValuedSignal.aux_foldl_set_mapTime (sig : FourValuedSignal 𝕋)
    (L : List (STLInterval 𝕋)) (v : FourValued) : -- --- CONCL ---
    (L.foldl (fun sig I => sig.set I v) sig).mapTime toReal =
      (L.map STLInterval.toRealInterval).foldl (fun sig I => sig.set I v)
        (sig.mapTime toReal) := by -- --- PROOF ---
  -- one interval at a time
  induction L generalizing sig with
  | nil => rfl
  | cons I L ih => simp only [List.foldl_cons, List.map_cons, ih, FourValuedSignal.set_mapTime]


-- =======================================  MAIN THEOREM  ======================================= --

theorem FourValuedSignal.merge_mapTime (obj other : FourValuedSignal 𝕋) :
    (obj.merge other).mapTime toReal = (obj.mapTime toReal).merge (other.mapTime toReal) := by
  simp only [FourValuedSignal.merge, FourValuedSignal.aux_foldl_set_mapTime,
    FourValuedSignal.findIntervals_mapTime]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
