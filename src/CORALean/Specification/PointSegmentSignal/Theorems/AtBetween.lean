module

public import CORALean.Specification.PointSegmentSignal.Definitions.IsValid
public import CORALean.Specification.PointSegmentSignal.Operations.At
public import CORALean.Specification.PointSegmentSignal.Operations.Basic
public import CORALean.Specification.PointSegmentSignal.Theorems.ListLengthTakeWhileEqOfPairwiseLt

@[expose] public section

/-!
# The value of a signal between time points

After the `i`-th time point of a valid signal and before the next one (or with no next one) the
signal has the interval value stored for that point.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem PointSegmentSignal.at_between {T : Type} [LinearOrder T] [Zero T]
    (s : PointSegmentSignal T) (hs : s.IsValid) (i : ℕ) (a t : T)
    (ha : s.timePoints[i]? = some a) (h1 : a < t)
    (h2 : ∀ b, s.timePoints[i + 1]? = some b → t < b) : -- --- CONCL ---
    s.at t = s.succIntervalValue (i + 1) := by -- --- PROOF ---
  have hlen := List.length_takeWhile_eq_of_pairwise_lt s.timePoints hs.2.2.2.1 t a i ha h1.le h2
  have hne : s.timePoints[i]? ≠ some t := by rw [ha]; simpa using h1.ne
  simp only [PointSegmentSignal.at, hlen, Nat.add_sub_cancel, hne, if_false,
    PointSegmentSignal.succIntervalValue, show 2 * (i + 1) - 1 = 2 * i + 1 by omega]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
