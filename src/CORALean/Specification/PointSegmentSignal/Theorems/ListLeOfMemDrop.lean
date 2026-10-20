module

public import CORALean.Specification.PointSegmentSignal.PointSegmentSignal
public import Mathlib.Order.Basic

@[expose] public section

/-!
# Entries from an index of a strictly increasing list

Every entry among those from index `m` on of a strictly increasing list is at least the entry at
`m`.

## Inputs
* `l` – list
* `m` – index
* `b` – entry at the index
* `x` – entry from the index on

## Hypotheses
* `hl` – the list strictly increases
* `hb` – the entry is at the index
* `hx` – the other entry is from the index on

## Conclusion
* the entry is at most the later one
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {T : Type} [LinearOrder T]


-- =======================================  MAIN THEOREM  ======================================= --

/-- An entry from `m` on is at least the entry at `m`. -/
theorem List.le_of_mem_drop (l : List T) (hl : l.Pairwise (· < ·)) (m : ℕ) (b : T)
    (hb : l[m]? = some b) (x : T) (hx : x ∈ l.drop m) : -- --- CONCL ---
    b ≤ x := by -- --- PROOF ---
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
  simp only [List.length_drop] at hk
  rw [List.getElem_drop]
  obtain ⟨hm, rfl⟩ := List.getElem?_eq_some_iff.mp hb
  rcases Nat.eq_zero_or_pos k with rfl | h
  · simp
  · exact (List.pairwise_iff_getElem.mp hl m (m + k) hm (by omega) (by omega)).le

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
