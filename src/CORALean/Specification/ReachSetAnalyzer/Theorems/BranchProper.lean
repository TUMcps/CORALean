module

public import CORALean.Specification.ReachSetAnalyzer.Definitions.IsBranch
public import CORALean.Specification.ReachSetAnalyzer.Operations.Basic

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


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The children are entries. -/
private theorem ReachSetAnalyzer.aux_children_mem (R : List (ReachSetAnalyzer.Entry ℝ S n))
    (i j : ℕ) (h : j ∈ ReachSetAnalyzer.children R i) : -- --- CONCL ---
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


/-- A branch names entries. -/
private theorem ReachSetAnalyzer.aux_branch_entries
    (R : List (ReachSetAnalyzer.Entry ℝ S n)) : -- --- CONCL ---
    ∀ (i : ℕ) (w : List ℕ), ReachSetAnalyzer.IsBranch (ReachSetAnalyzer.children R) i w →
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
    have hchild := (ReachSetAnalyzer.aux_children_mem R i j0 hj0).2
    rcases List.mem_append.mp hj with hj | hj
    · by_cases h0 : i ≠ 0
      · rw [if_pos h0] at hj
        obtain rfl : j = i := by simpa using hj
        exact hi.resolve_left h0
      · simp [h0] at hj
    · exact ih (Or.inr (by obtain ⟨e, he, -⟩ := hchild; exact ⟨e, he⟩)) j hj


-- =======================================  MAIN THEOREM  ======================================= --

theorem ReachSetAnalyzer.branch_proper (R : List (ReachSetAnalyzer.Entry ℝ S n))
    (hR : ∀ e ∈ R, ∀ s ∈ e.timeInterval, s.time.inf < s.time.sup) (w : List ℕ)
    (hw : ReachSetAnalyzer.IsBranch (ReachSetAnalyzer.children R) 0 w) :
    ∀ j ∈ w, ∃ e, R[j - 1]? = some e ∧
      ∀ s ∈ e.timeInterval, s.time.inf < s.time.sup := fun j hj => by
  obtain ⟨e, he⟩ := ReachSetAnalyzer.aux_branch_entries R 0 w hw (Or.inl rfl) j hj
  exact ⟨e, he, hR e (List.mem_of_getElem? he)⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
