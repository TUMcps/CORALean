module

public import CORALean.Specification.PointSegmentSignal.PointSegmentSignal
public import Mathlib.Data.List.Basic

@[expose] public section

/-!
# Membership in a slice of a list

An entry of the slice `(l.take a).drop b` is an entry of `l` at an index from `b` up to before `a`.

## Inputs
* `α` – element type
* `l` – list
* `a` – upper index
* `b` – lower index
* `x` – entry

## Hypotheses
* none

## Conclusion
* the entry is in the slice iff it sits at an index in the range
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- The entries of `(l.take a).drop b` are those of `l` at the indices from `b` to before `a`. -/
theorem List.mem_take_drop_iff {α : Type} (l : List α) (a b : ℕ) (x : α) :
    x ∈ (l.take a).drop b ↔ ∃ m, b ≤ m ∧ m < a ∧ ∃ h : m < l.length, l[m] = x := by -- --- PROOF ---
  rw [List.mem_iff_getElem?]
  constructor
  · rintro ⟨j, hj⟩
    rw [List.getElem?_drop, List.getElem?_take] at hj
    by_cases hja : b + j < a
    · rw [if_pos hja] at hj
      obtain ⟨hl, hx⟩ := List.getElem?_eq_some_iff.1 hj
      exact ⟨b + j, by omega, hja, hl, hx⟩
    · simp [hja] at hj
  · rintro ⟨m, hb, ha, hl, hx⟩
    refine ⟨m - b, ?_⟩
    rw [List.getElem?_drop, List.getElem?_take, if_pos (by omega), show b + (m - b) = m by omega,
      List.getElem?_eq_getElem hl, hx]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
