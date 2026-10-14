module

public import CORALean.Specification.PointSegmentSignal.PointSegmentSignal
public import Mathlib.Order.Basic

@[expose] public section

/-!
# Consecutive entries of a strictly increasing list

In a strictly increasing list the entry at `m` is below the entry at `m + 1`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem List.lt_of_pairwise_getElem_succ {T : Type} [LinearOrder T] {l : List T}
    (hl : l.Pairwise (· < ·)) {m : ℕ} {a b : T} (ha : l[m]? = some a) (hb : l[m + 1]? = some b) :
    a < b := by
  rw [List.pairwise_iff_getElem] at hl
  obtain ⟨hm, rfl⟩ := List.getElem?_eq_some_iff.mp ha
  obtain ⟨hm', rfl⟩ := List.getElem?_eq_some_iff.mp hb
  exact hl m (m + 1) hm hm' (by omega)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
