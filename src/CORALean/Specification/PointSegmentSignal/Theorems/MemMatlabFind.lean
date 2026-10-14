module

public import CORALean.Specification.PointSegmentSignal.Operations.Basic

@[expose] public section

/-!
# Membership in `find`

An index is found by `find(x)` with a predicate exactly when it is a one-based index of an entry
that satisfies it.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- Membership in `find`: a one-based index of an entry satisfying the predicate. -/
theorem List.mem_matlabFind {α : Type} (p : α → Bool) (l : List α) (j : ℕ) :
    j ∈ List.matlabFind p l ↔
      1 ≤ j ∧ ∃ h : j - 1 < l.length, p l[j - 1] = true := by -- --- PROOF ---
  simp only [List.matlabFind, List.mem_filter, List.mem_range'_1]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    have hj : j - 1 < l.length := by omega
    refine ⟨h1, hj, ?_⟩
    simpa [List.getElem?_eq_getElem hj] using h3
  · rintro ⟨h1, hj, h3⟩
    refine ⟨⟨h1, by omega⟩, ?_⟩
    simpa [List.getElem?_eq_getElem hj] using h3

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
