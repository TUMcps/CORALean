module

public import CORALean.Specification.STLInterval.Theorems.NonemptySetSubsetIff

@[expose] public section

/-!
# An STL interval is determined by its times

Two intervals denoting the same set are equal: the bounds and the flags are those of the set. So
the constructor's normal form (the empty interval, an infinite end open) is canonical.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* an interval is determined by its times
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- `STLInterval.set` is injective. -/
theorem STLInterval.set_injective : -- --- CONCL ---
    Function.Injective STLInterval.set := by -- --- PROOF ---
  intro I J h
  -- an empty interval equals only an empty one
  cases I with
  | empty =>
    cases J with
    | empty => rfl
    | nonempty l u lc rc a b c _ =>
      exact absurd h.symm (Set.nonempty_iff_ne_empty.1 (rawSet_nonempty_of _ _ _ _ a b c))
  | nonempty l₁ u₁ lc₁ rc₁ a₁ b₁ c₁ z₁ =>
    -- two nonempty intervals include each other, so the bounds and flags agree
    cases J with
    | empty =>
      exact absurd h (Set.nonempty_iff_ne_empty.1 (rawSet_nonempty_of _ _ _ _ a₁ b₁ c₁))
    | nonempty l₂ u₂ lc₂ rc₂ a₂ b₂ c₂ z₂ =>
      have h12 := (nonempty_set_subset_iff a₁ b₁ c₁ a₂ b₂ c₂ z₁ z₂).1 h.symm.subset
      have h21 := (nonempty_set_subset_iff a₂ b₂ c₂ a₁ b₁ c₁ z₂ z₁).1 h.subset
      have hl : l₁ = l₂ := by
        rcases h12.1 with h1 | ⟨e, _⟩
        · rcases h21.1 with h2 | ⟨e, _⟩
          · exact (lt_asymm h1 h2).elim
          · exact (ne_of_lt h1 e.symm).elim
        · exact e
      have hu : u₁ = u₂ := by
        rcases h12.2 with h1 | ⟨e, _⟩
        · rcases h21.2 with h2 | ⟨e, _⟩
          · exact (lt_asymm h1 h2).elim
          · exact (ne_of_lt h1 e).elim
        · exact e
      -- the bounds agree, and then the flags
      subst hl hu
      have hlc : lc₁ = lc₂ := by
        have := h12.1; have := h21.1
        cases lc₁ <;> cases lc₂ <;> simp_all
      have hrc : rc₁ = rc₂ := by
        have := h12.2; have := h21.2
        cases rc₁ <;> cases rc₂ <;> simp_all
      subst hlc hrc
      rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
