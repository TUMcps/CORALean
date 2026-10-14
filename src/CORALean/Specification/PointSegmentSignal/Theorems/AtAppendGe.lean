module

public import CORALean.Specification.PointSegmentSignal.Operations.At
public import Mathlib.Data.List.GetD
public import Mathlib.Data.List.TakeWhile
public import Mathlib.Order.Basic

@[expose] public section

/-!
# Appended points take over from their first point on

At a time `t` at or after the first point of an appended block (and after the earlier points), the
value is the block's own.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {T : Type} [LinearOrder T]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Past the first appended point the signal is the appended block. -/
theorem PointSegmentSignal.at_append_ge (A : List T) (r : T) (R : List T) (VA VR : List Bool)
    (t : T) (hlen : VA.length = 2 * A.length) (hA : ∀ a ∈ A, a ≤ t) (hr : r ≤ t) :
    (PointSegmentSignal.mk (A ++ r :: R) (VA ++ VR)).at t = (PointSegmentSignal.mk (r :: R) VR).at t
      := by -- --- PROOF ---
  have h1 : (A ++ r :: R).takeWhile (· ≤ t) = A ++ (r :: R).takeWhile (· ≤ t) :=
    List.takeWhile_append_of_pos (by simpa using hA)
  have hL : 0 < ((r :: R).takeWhile (· ≤ t)).length := by simp [hr]
  simp only [PointSegmentSignal.at, h1, List.length_append]
  have e : A.length + ((r :: R).takeWhile (· ≤ t)).length - 1 =
      A.length + (((r :: R).takeWhile (· ≤ t)).length - 1) := by omega
  rw [e, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    show 2 * (A.length + (((r :: R).takeWhile (· ≤ t)).length - 1)) =
      VA.length + 2 * (((r :: R).takeWhile (· ≤ t)).length - 1) by omega]
  rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
  simp [Nat.add_assoc, Nat.add_sub_cancel_left]


-- takeWhile facts (any list)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
