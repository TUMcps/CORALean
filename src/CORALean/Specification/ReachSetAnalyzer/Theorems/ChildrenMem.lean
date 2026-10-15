module

public import CORALean.Specification.ReachSetAnalyzer.Operations.Basic

@[expose] public section

/-!
# The children are entries

An index `j` in `children(R,i)` names an entry: `R(j)` exists (CORA numbers from `1`), and its
parent is `i`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S : ℕ → Type} {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ReachSetAnalyzer.children_mem (R : List (ReachSetAnalyzer.Entry S n)) (i j : ℕ)
    (h : j ∈ ReachSetAnalyzer.children R i) :
    1 ≤ j ∧ ∃ e, R[j - 1]? = some e ∧ e.parent = i := by -- --- PROOF ---
  unfold ReachSetAnalyzer.children at h
  obtain ⟨idx, -, hidx⟩ := List.mem_filterMap.mp h
  by_cases hc : R[idx]?.map (·.parent) = some i
  · rw [if_pos hc] at hidx
    obtain rfl : idx + 1 = j := Option.some.inj hidx
    obtain ⟨e, he, hp⟩ := Option.map_eq_some_iff.mp hc
    exact ⟨by omega, e, by simpa using he, hp⟩
  · rw [if_neg hc] at hidx
    exact absurd hidx (by simp)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
