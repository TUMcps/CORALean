module

public import CORALean.Specification.PointSegmentSignal.Definitions.IsValid
public import CORALean.Specification.PointSegmentSignal.Operations.At
public import CORALean.Specification.PointSegmentSignal.Operations.Basic
public import CORALean.Specification.PointSegmentSignal.Theorems.ListLengthTakeWhileEqOfPairwiseLt
public import CORALean.Specification.PointSegmentSignal.Theorems.ListLtOfPairwiseGetElemSucc

@[expose] public section

/-!
# The value of a signal at a time point

At the `i`-th time point of a valid signal (counted from `1`) the signal has the point value
stored for it.

## Inputs
* `T` – time type
* `s` – signal
* `i` – time point index
* `a` – the time point

## Hypotheses
* `hs` – the signal is valid
* `ha` – the point is the one at that index

## Conclusion
* the value at the point is its point value
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem PointSegmentSignal.at_timePoint {T : Type} [LinearOrder T] [Zero T]
    (s : PointSegmentSignal T) (hs : s.IsValid) (i : ℕ) (a : T) (ha : s.timePoints[i]? = some a) :
    s.at a = s.pointValue (i + 1) := by
  have hlen := List.length_takeWhile_eq_of_pairwise_lt s.timePoints hs.2.2.2.1 a a i ha le_rfl
    (fun b hb => List.lt_of_pairwise_getElem_succ hs.2.2.2.1 ha hb)
  simp only [PointSegmentSignal.at, hlen, Nat.add_sub_cancel, ha, TimeOrder.exists_mem_eqv_iff,
    if_true, PointSegmentSignal.pointValue, show 2 * (i + 1) - 2 = 2 * i by omega]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
