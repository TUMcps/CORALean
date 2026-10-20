module

public import CORALean.Specification.STL.Operations.TreeAssignIdentifiersFrom

@[expose] public section

/-!
# What assignIdentifiers collects is non-temporal

Every formula `assignIdentifiers` adds to its list is non-temporal: the walk stops at a maximal
non-temporal sub-formula and a temporal operator is always entered.

## Inputs
* `φ` – formula
* `list` – formulas numbered so far
* `ψ` – subformula

## Hypotheses
* `h` – the subformula is in the new list

## Conclusion
* the subformula was in the old list or is non-temporal
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.Tree.temporal_of_mem_assignIdentifiersFrom (φ : STL.Tree n) (list : List (STL.Tree n))
    (ψ : STL.Tree n) (h : ψ ∈ φ.assignIdentifiersFrom list) : -- --- CONCL ---
    ψ ∈ list ∨ ψ.temporal = false := by -- --- PROOF ---
  induction φ generalizing list with
  -- a leaf is appended to the list
  | tt | ff | cmp op e₁ e₂ =>
    simp only [STL.Tree.assignIdentifiersFrom, List.mem_append, List.mem_singleton] at h
    rcases h with h | rfl
    · exact Or.inl h
    · exact Or.inr rfl
  -- `~` enters a temporal operand and stops at a non-temporal one
  | not φ ih =>
    simp only [STL.Tree.assignIdentifiersFrom] at h
    split_ifs at h with hφ
    · exact ih _ h
    · rcases List.mem_append.1 h with h | h
      · exact Or.inl h
      · obtain rfl := List.mem_singleton.1 h
        exact Or.inr (by simpa [STL.Tree.temporal] using hφ)
  -- the same for `&` and `|`, the left operand first
  | and φ χ ihφ ihχ | or φ χ ihφ ihχ =>
    simp only [STL.Tree.assignIdentifiersFrom] at h
    split_ifs at h with hc
    · rcases ihχ _ h with h | h
      · exact ihφ _ h
      · exact Or.inr h
    · rcases List.mem_append.1 h with h | h
      · exact Or.inl h
      · obtain rfl := List.mem_singleton.1 h
        exact Or.inr (by simpa [STL.Tree.temporal] using hc)
  -- the temporal operators enter their operands
  | next a φ ih | «finally» a b φ ih | globally a b φ ih => exact ih _ h
  | «until» a b φ χ ihφ ihχ | release a b φ χ ihφ ihχ =>
    rcases ihχ _ h with h | h
    · exact ihφ _ h
    · exact Or.inr h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
