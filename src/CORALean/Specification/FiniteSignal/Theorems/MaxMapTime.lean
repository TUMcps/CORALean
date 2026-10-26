module

public import CORALean.Global.Float.TimeOrder
public import CORALean.Specification.FiniteSignal.Operations.Basic
public import CORALean.Specification.FiniteSignal.Operations.Max
public import Mathlib.Algebra.Ring.BooleanRing

@[expose] public section

/-!
# The maximum of a float signal on an interval, read as reals

Over a float scalar `max` finds the breakpoints around the bounds by exact comparisons
(`TimeOrder`), so the maximum of the float signal on `[lo, hi]` is that of the signal read as reals
on the reals the bounds denote.

## Inputs
* `s` – signal
* `lo` – interval lower bound
* `hi` – interval upper bound

## Hypotheses
* none

## Conclusion
* the maximum is that of the signal read as reals
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

theorem FiniteSignal.max_mapTime (s : FiniteSignal 𝕋 Bool) (lo hi : 𝕋) : -- --- CONCL ---
    (s.mapTime toReal).max (toReal lo) (toReal hi) = s.max lo hi := by -- --- PROOF ---
  unfold FiniteSignal.max FiniteSignal.mapTime FiniteSignal.length
  simp only [List.length_map]
  -- the first loop stops at the same breakpoint
  have hk : (List.takeWhile (fun t => decide (t < toReal lo)) (s.time.map toReal)).length =
      (List.takeWhile (fun t => decide (t < lo)) s.time).length := by
    rw [List.takeWhile_map, List.length_map]
    exact congrArg List.length (congrArg (List.takeWhile · s.time)
      (funext fun t => decide_eq_decide.mpr Iff.rfl))
  rw [hk]
  congr 1
  -- the second loop takes the same breakpoints
  funext v j
  have hg : (s.time.map toReal).getD j 0 = toReal (s.time.getD j 0) := by
    rw [← toReal_zero_eq (𝕋 := 𝕋), List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_map]
    cases s.time[j]? <;> rfl
  rw [hg]
  by_cases h : s.time.getD j 0 ≤ hi
  · rw [if_pos h, if_pos (show toReal (s.time.getD j 0) ≤ toReal hi from h)]
  · rw [if_neg h, if_neg (show ¬ toReal (s.time.getD j 0) ≤ toReal hi from h)]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
