module

public import CORALean.Specification.PointSegmentSignal.Definitions.IsValid
public import Mathlib.Order.Basic

@[expose] public section

/-!
# The time points of a signal are nonnegative

Every time point of a valid signal is `≥ 0`: the first is `0` and they increase.

## Inputs
* `T` – time type
* `s` – signal
* `x` – time point

## Hypotheses
* `hs` – the signal is valid
* `hx` – the point is a time point of the signal

## Conclusion
* the time point is nonnegative
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem PointSegmentSignal.nonneg_of_mem_timePoints {T : Type} [LinearOrder T] [Zero T]
    (s : PointSegmentSignal T) (hs : s.IsValid) (x : T) (hx : x ∈ s.timePoints) :
    0 ≤ x := by -- --- PROOF ---
  obtain ⟨-, -, hhead, hsort, -⟩ := hs
  obtain ⟨a, l, hl⟩ : ∃ a l, s.timePoints = a :: l := by
    cases h : s.timePoints with
    | nil => simp [h] at hhead
    | cons a l => exact ⟨a, l, rfl⟩
  rw [hl] at hhead hsort hx
  simp only [List.head?_cons, Option.some.injEq] at hhead
  subst hhead
  rcases List.mem_cons.mp hx with rfl | hx
  · exact le_rfl
  · exact (List.pairwise_cons.mp hsort).1 x hx |>.le

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
