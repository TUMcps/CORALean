module

public import CORALean.Specification.PointSegmentSignal.PointSegmentSignal
public import Mathlib.Order.Basic

@[expose] public section

/-!
# Entries up to an index of a strictly increasing list

Every entry among the first `m + 1` of a strictly increasing list is at most the entry at `m`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {T : Type} [LinearOrder T]


-- =======================================  MAIN THEOREM  ======================================= --

/-- An entry of the first `m + 1` is at most the entry at `m`. -/
theorem List.le_of_mem_take_succ (l : List T) (hl : l.Pairwise (· < ·)) (m : ℕ) (a : T)
    (ha : l[m]? = some a) (x : T) (hx : x ∈ l.take (m + 1)) :
    x ≤ a := by -- --- PROOF ---
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
  simp only [List.length_take] at hk
  rw [List.getElem_take]
  obtain ⟨hm, rfl⟩ := List.getElem?_eq_some_iff.mp ha
  rcases Nat.lt_or_ge k m with h | h
  · exact (List.pairwise_iff_getElem.mp hl k m (by omega) hm h).le
  · have : k = m := by omega
    subst this; exact le_rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
