module

public import CORALean.Specification.ReachSetAnalyzer.Theorems.BranchEntries

@[expose] public section

/-!
# The entries of a branch have proper time intervals

If all time intervals of the entries of `R` are proper (`lo < hi`), so are those of the entries
a branch of the tree of `R` names.

## Inputs
* `R` – tree of reach sets
* `w` – branch from the root

## Hypotheses
* `hR` – all time intervals are proper
* `hw` – the indices form a branch from the root

## Conclusion
* the branch's entries have proper time intervals
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S : ℕ → Type} {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ReachSetAnalyzer.branch_proper (R : List (ReachSetAnalyzer.Entry S n))
    (hR : ∀ e ∈ R, ∀ s ∈ e.timeInterval, s.time.inf < s.time.sup) (w : List ℕ)
    (hw : ReachSetAnalyzer.Branch (ReachSetAnalyzer.children R) 0 w) :
    ∀ j ∈ w, ∃ e, R[j - 1]? = some e ∧
      ∀ s ∈ e.timeInterval, s.time.inf < s.time.sup := fun j hj => by
  obtain ⟨e, he⟩ := ReachSetAnalyzer.branch_entries R 0 w hw (Or.inl rfl) j hj
  exact ⟨e, he, hR e (List.mem_of_getElem? he)⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
