module

public import CORALean.Specification.ReachSetAnalyzer.Definitions.Branch
public import CORALean.Specification.ReachSetAnalyzer.Theorems.ChildrenMem

@[expose] public section

/-!
# A branch names entries

Every index on a branch of the tree of `R` that starts at the root or at an entry names an entry
of `R`.

## Inputs
* `R` – tree of reach sets

## Hypotheses
* none

## Conclusion
* every index on a branch names an entry
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S : ℕ → Type} {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ReachSetAnalyzer.branch_entries (R : List (ReachSetAnalyzer.Entry S n)) : -- --- CONCL ---
    ∀ (i : ℕ) (w : List ℕ), ReachSetAnalyzer.Branch (ReachSetAnalyzer.children R) i w →
      (i = 0 ∨ ∃ e, R[i - 1]? = some e) → ∀ j ∈ w, ∃ e, R[j - 1]? = some e := by -- --- PROOF ---
  intro i w hw
  induction hw with
  | leaf i _ =>
    intro hi j hj
    by_cases h0 : i ≠ 0
    · rw [if_pos h0] at hj
      obtain rfl : j = i := by simpa using hj
      exact hi.resolve_left h0
    · simp [h0] at hj
  | node i j0 w hj0 _ ih =>
    intro hi j hj
    have hchild := (ReachSetAnalyzer.children_mem R i j0 hj0).2
    rcases List.mem_append.mp hj with hj | hj
    · by_cases h0 : i ≠ 0
      · rw [if_pos h0] at hj
        obtain rfl : j = i := by simpa using hj
        exact hi.resolve_left h0
      · simp [h0] at hj
    · exact ih (Or.inr (by obtain ⟨e, he, -⟩ := hchild; exact ⟨e, he⟩)) j hj

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
