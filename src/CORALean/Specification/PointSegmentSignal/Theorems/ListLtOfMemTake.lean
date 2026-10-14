module

public import CORALean.Specification.PointSegmentSignal.PointSegmentSignal
public import Mathlib.Order.Basic

@[expose] public section

/-!
# Entries before an index of a strictly increasing list

Every entry before index `m` of a strictly increasing list is below the entry at `m`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {T : Type} [LinearOrder T]


-- =======================================  MAIN THEOREM  ======================================= --

/-- An entry of the first `m` is below the entry at `m`. -/
theorem List.lt_of_mem_take (l : List T) (hl : l.Pairwise (· < ·)) (m : ℕ) (a : T)
    (ha : l[m]? = some a) (x : T) (hx : x ∈ l.take m) :
    x < a := by -- --- PROOF ---
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
  simp only [List.length_take] at hk
  rw [List.getElem_take]
  obtain ⟨hm, rfl⟩ := List.getElem?_eq_some_iff.mp ha
  exact List.pairwise_iff_getElem.mp hl k m (by omega) hm (by omega)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
