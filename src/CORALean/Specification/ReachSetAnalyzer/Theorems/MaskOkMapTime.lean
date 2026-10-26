module

public import CORALean.Global.LookupMapSnd
public import CORALean.Specification.FiniteSignal.Theorems.MaxMapTime
public import CORALean.Specification.ReachSetAnalyzer.Operations.Basic
public import CORALean.Specification.ReachSetAnalyzer.Operations.MaskOk

@[expose] public section

/-!
# The mask of a float analyzer, read as reals

Over a float scalar `maskOk` looks the mask up by its key and takes its maximum on the interval
with exact comparisons (`max_mapTime`), so a float analyzer lets an interval through as the analyzer
read as reals lets the interval read as reals through.

## Inputs
* `obj` – analyzer
* `k` – proposition key
* `lo` – interval lower bound
* `hi` – interval upper bound

## Hypotheses
* none

## Conclusion
* the float test is the test of the analyzer read as reals
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋] {S : ℕ → Type} {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ReachSetAnalyzer.maskOk_mapTime (obj : ReachSetAnalyzer 𝕋 S n) (k : String)
    (lo hi : 𝕋) : -- --- CONCL ---
    (obj.mapTime toReal).maskOk k (toReal lo) (toReal hi) =
      obj.maskOk k lo hi := by -- --- PROOF ---
  unfold ReachSetAnalyzer.maskOk ReachSetAnalyzer.mapTime
  simp only
  rw [lookup_map_snd]
  cases obj.masks.lookup k with
  | none => rfl
  | some m => exact FiniteSignal.max_mapTime m lo hi

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
