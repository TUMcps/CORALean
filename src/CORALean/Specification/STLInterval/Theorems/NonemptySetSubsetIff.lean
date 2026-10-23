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

## Inputs
* `x₁` – lower bound of the outer interval
* `x₂` – lower bound of the inner interval
* `v₁` – upper bound of the outer interval
* `v₂` – upper bound of the inner interval
* `lc₁` – outer lower bound is closed
* `rc₁` – outer upper bound is closed
* `lc₂` – inner lower bound is closed
* `rc₂` – inner upper bound is closed

## Hypotheses
* `b₁` – an infinite outer upper bound is open
* `c₁` – the outer interval is nonempty
* `b₂` – an infinite inner upper bound is open
* `c₂` – the inner interval is nonempty
* `z₁` – the outer lower bound is nonnegative
* `z₂` – the inner lower bound is nonnegative

## Conclusion
* the inner interval lies in the outer iff its bounds lie inside
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Containment of nonempty STL intervals, bound by bound. -/
theorem STLInterval.nonempty_set_subset_iff {x₁ x₂ : 𝕋} {v₁ v₂ : WithTop 𝕋}
    {lc₁ rc₁ lc₂ rc₂ : Bool} (b₁ : v₁ = ⊤ → rc₁ = false)
    (c₁ : ((toReal x₁ : ℝ) : EReal) < toEReal v₁ ∨
      ((toReal x₁ : ℝ) : EReal) = toEReal v₁ ∧ lc₁ = true ∧ rc₁ = true)
    (b₂ : v₂ = ⊤ → rc₂ = false)
    (c₂ : ((toReal x₂ : ℝ) : EReal) < toEReal v₂ ∨
      ((toReal x₂ : ℝ) : EReal) = toEReal v₂ ∧ lc₂ = true ∧ rc₂ = true) (z₁ : 0 ≤ toReal x₁)
    (z₂ : 0 ≤ toReal x₂) : -- --- CONCL ---
    (STLInterval.nonempty x₂ v₂ lc₂ rc₂ b₂ c₂ z₂).set ⊆
        (STLInterval.nonempty x₁ v₁ lc₁ rc₁ b₁ c₁ z₁).set ↔
      (((toReal x₁ : ℝ) : EReal) < (toReal x₂ : ℝ) ∨
        (((toReal x₁ : ℝ) : EReal) = (toReal x₂ : ℝ) ∧ (lc₁ = true ∨ lc₂ = false))) ∧
        (toEReal v₂ < toEReal v₁ ∨
          (toEReal v₁ = toEReal v₂ ∧ (rc₁ = true ∨ rc₂ = false))) := by -- --- PROOF ---
  -- the extended-real bounds, with the facts the fields give about them
  have a₁ : ((toReal x₁ : ℝ) : EReal) = ⊥ → lc₁ = false := fun h => absurd h (EReal.coe_ne_bot _)
  have a₂ : ((toReal x₂ : ℝ) : EReal) = ⊥ → lc₂ = false := fun h => absurd h (EReal.coe_ne_bot _)
  have b₁' : toEReal v₁ = ⊤ → rc₁ = false := fun h => b₁ ((toEReal_eq_top_iff v₁).1 h)
  have b₂' : toEReal v₂ = ⊤ → rc₂ = false := fun h => b₂ ((toEReal_eq_top_iff v₂).1 h)
  show rawSet _ _ lc₂ rc₂ ⊆ rawSet _ _ lc₁ rc₁ ↔ _
  clear z₁ z₂
  generalize ((toReal x₁ : ℝ) : EReal) = l₁ at *
  generalize ((toReal x₂ : ℝ) : EReal) = l₂ at *
  generalize toEReal v₁ = u₁ at *
  generalize toEReal v₂ = u₂ at *
  have h₁ := rawSet_nonempty_of _ _ _ _ a₁ b₁' c₁
  have h₂ := rawSet_nonempty_of _ _ _ _ a₂ b₂' c₂
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
        have ht : u₂ ≠ ⊤ := fun h' => by simp [b₂' h'] at hc
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
