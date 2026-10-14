module

public import CORALean.Specification.STLInterval.Theorems.Basic
public import CORALean.Specification.STLInterval.Theorems.RawSetLowerReach
public import CORALean.Specification.STLInterval.Theorems.RawSetUpperReach
public import CORALean.Specification.STLInterval.Theorems.RawSetBoundsNe

@[expose] public section

/-!
# When one STL interval lies in another

`J ⊆ I` for two nonempty intervals iff `I`'s lower bound is below `J`'s (or equal, `I`'s end closed
or `J`'s open) and the same for the upper bounds: the test of `@stlInterval/contains_.m`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- Containment of nonempty STL intervals, bound by bound. -/
theorem STLInterval.nonempty_set_subset_iff {l₁ u₁ l₂ u₂ : EReal} {lc₁ rc₁ lc₂ rc₂ : Bool}
    (a₁ : l₁ = ⊥ → lc₁ = false) (b₁ : u₁ = ⊤ → rc₁ = false)
    (c₁ : l₁ < u₁ ∨ l₁ = u₁ ∧ lc₁ = true ∧ rc₁ = true)
    (a₂ : l₂ = ⊥ → lc₂ = false) (b₂ : u₂ = ⊤ → rc₂ = false)
    (c₂ : l₂ < u₂ ∨ l₂ = u₂ ∧ lc₂ = true ∧ rc₂ = true) :
    (STLInterval.nonempty l₂ u₂ lc₂ rc₂ a₂ b₂ c₂).set ⊆
        (STLInterval.nonempty l₁ u₁ lc₁ rc₁ a₁ b₁ c₁).set ↔
      (l₁ < l₂ ∨ (l₁ = l₂ ∧ (lc₁ = true ∨ lc₂ = false))) ∧
        (u₂ < u₁ ∨ (u₁ = u₂ ∧ (rc₁ = true ∨ rc₂ = false))) := by -- --- PROOF ---
  have h₁ := set_nonempty _ _ _ _ a₁ b₁ c₁
  have h₂ := set_nonempty _ _ _ _ a₂ b₂ c₂
  constructor
  -- containment passes each test of `J` to `I`, through the reaches of both
  · intro H
    have hlow : ∀ s : ℝ, (l₂ < s ∨ (lc₂ = true ∧ l₂ = s)) → (l₁ < s ∨ (lc₁ = true ∧ l₁ = s)) := by
      intro s hs
      obtain ⟨t, ht, hts⟩ := (rawSet_lowerReach h₂ s).2 hs
      exact (rawSet_lowerReach h₁ s).1 ⟨t, H ht, hts⟩
    have hup : ∀ s : ℝ, ((s : EReal) < u₂ ∨ (rc₂ = true ∧ (s : EReal) = u₂)) →
        ((s : EReal) < u₁ ∨ (rc₁ = true ∧ (s : EReal) = u₁)) := by
      intro s hs
      obtain ⟨t, ht, hts⟩ := (rawSet_upperReach h₂ s).2 hs
      exact (rawSet_upperReach h₁ s).1 ⟨t, H ht, hts⟩
    constructor
    -- the lower bounds: `l₁ < l₂`, or equal with the flags that allow it
    · rcases lt_trichotomy l₁ l₂ with h | h | h
      · exact Or.inl h
      · refine Or.inr ⟨h, ?_⟩
        by_contra hc
        simp only [not_or, Bool.not_eq_true, Bool.not_eq_false] at hc
        have hb : l₂ ≠ ⊥ := fun h' => by simp [a₂ h'] at hc
        have ht := (rawSet_bounds_ne h₂).1
        rcases hlow l₂.toReal (Or.inr ⟨hc.2, (EReal.coe_toReal ht hb).symm⟩) with h' | ⟨h', _⟩
        · rw [EReal.coe_toReal ht hb, h] at h'; exact lt_irrefl _ h'
        · simp [hc.1] at h'
      · obtain ⟨s, hs1, hs2⟩ := EReal.exists_between_coe_real h
        rcases hlow s (Or.inl hs1) with h' | ⟨_, h'⟩
        · exact (lt_asymm h' hs2).elim
        · exact (lt_irrefl _ (h' ▸ hs2)).elim
    -- the upper bounds, the same way
    · rcases lt_trichotomy u₂ u₁ with h | h | h
      · exact Or.inl h
      · refine Or.inr ⟨h.symm, ?_⟩
        by_contra hc
        simp only [not_or, Bool.not_eq_true, Bool.not_eq_false] at hc
        have ht : u₂ ≠ ⊤ := fun h' => by simp [b₂ h'] at hc
        have hb := (rawSet_bounds_ne h₂).2
        rcases hup u₂.toReal (Or.inr ⟨hc.2, EReal.coe_toReal ht hb⟩) with h' | ⟨h', _⟩
        · rw [EReal.coe_toReal ht hb, h] at h'; exact lt_irrefl _ h'
        · simp [hc.1] at h'
      · obtain ⟨s, hs1, hs2⟩ := EReal.exists_between_coe_real h
        rcases hup s (Or.inl hs2) with h' | ⟨_, h'⟩
        · exact (lt_asymm h' hs1).elim
        · exact (lt_irrefl _ (h' ▸ hs1)).elim
  -- conversely every member of `J` passes both tests of `I`
  · rintro ⟨hl, hu⟩ t ht
    refine ⟨?_, ?_⟩
    · rcases ht.1 with h | ⟨hc, h⟩
      · rcases hl with hl | ⟨e, _⟩
        · exact Or.inl (hl.trans h)
        · exact Or.inl (e ▸ h)
      · rcases hl with hl | ⟨e, hc'⟩
        · exact Or.inl (h ▸ hl)
        · exact Or.inr ⟨by simpa [hc] using hc', e.trans h⟩
    -- the upper test
    · rcases ht.2 with h | ⟨hc, h⟩
      · rcases hu with hu | ⟨e, _⟩
        · exact Or.inl (h.trans hu)
        · exact Or.inl (e ▸ h)
      · rcases hu with hu | ⟨e, hc'⟩
        · exact Or.inl (h ▸ hu)
        · exact Or.inr ⟨by simpa [hc] using hc', h.trans e.symm⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
