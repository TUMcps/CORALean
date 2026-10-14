module

public import CORALean.Specification.PointSegmentSignal.Operations.At
public import Mathlib.Data.List.GetD
public import Mathlib.Data.List.TakeWhile
public import Mathlib.Order.Basic

@[expose] public section

/-!
# Appending points above a time changes nothing at it

Appending a block of time points all above `t`, with any values, leaves the value at `t` of a
non-empty signal unchanged.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {T : Type} [LinearOrder T]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Appending points above `t` leaves the value at `t`. -/
theorem PointSegmentSignal.at_append_lt (A R : List T) (VA VR : List Bool)
    (hlen : VA.length = 2 * A.length) (hne : A ≠ []) (t : T) (h : ∀ r ∈ R, t < r) :
    (PointSegmentSignal.mk (A ++ R) (VA ++ VR)).at t = (PointSegmentSignal.mk A VA).at t
      := by -- --- PROOF ---
  have hpos : 0 < A.length := List.length_pos_iff.mpr hne
  have hL : (A.takeWhile (· ≤ t)).length ≤ A.length := (List.takeWhile_sublist _).length_le
  have hR : R.takeWhile (· ≤ t) = [] := by
    cases R with
    | nil => rfl
    | cons r R' => simp [not_le.mpr (h r (by simp))]
  have hlen' : ((A ++ R).takeWhile (· ≤ t)).length = (A.takeWhile (· ≤ t)).length := by
    rw [List.takeWhile_append]
    split_ifs with h1
    · simp [hR, h1]
    · rfl
  have hi : (A.takeWhile (· ≤ t)).length - 1 < A.length := by omega
  simp only [PointSegmentSignal.at, hlen']
  rw [List.getElem?_append_left hi, List.getD_append _ _ _ _ (by omega),
    List.getD_append _ _ _ _ (by omega)]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
