module

public import CORALean.Specification.STLInterval.Operations.And
public import CORALean.Specification.STLInterval.Theorems.SetStlInterval
public import CORALean.Specification.STLInterval.STLInterval

@[expose] public section

/-!
# `and_` denotes the intersection

`I & J` denotes the intersection of the two sets of times.

## Inputs
* `I` – first interval
* `J` – second interval

## Hypotheses
* none

## Conclusion
* the intersection denotes the intersection of the times
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The two lower tests together are the test of the larger bound. -/
private theorem STLInterval.rawSet_lower_and (l₁ l₂ : EReal) (lc₁ lc₂ : Bool)
    (t : EReal) : -- --- CONCL ---
    ((l₁ < t ∨ (lc₁ = true ∧ l₁ = t)) ∧ (l₂ < t ∨ (lc₂ = true ∧ l₂ = t))) ↔
      (max l₁ l₂ < t ∨ ((if l₂ < l₁ then lc₁ else if l₁ < l₂ then lc₂ else lc₁ && lc₂) = true ∧
        max l₁ l₂ = t)) := by -- --- PROOF ---
  rcases lt_trichotomy l₁ l₂ with h | h | h
  -- `l₁ < l₂`: the second operand supplies the bound
  · have : ¬ l₂ < l₁ := not_lt_of_gt h
    simp only [this, h, if_true, if_false, max_eq_right h.le]
    constructor
    · rintro ⟨a | ⟨ha, rfl⟩, b⟩
      · exact b
      · exact b
    · intro b
      refine ⟨?_, b⟩
      rcases b with b | ⟨hb, rfl⟩
      · exact Or.inl (h.trans b)
      · exact Or.inl h
  -- `l₁ = l₂`: both flags have to hold
  · subst h
    simp only [lt_self_iff_false, if_false, max_self]
    constructor
    · rintro ⟨a | ⟨ha, rfl⟩, b | ⟨hb, e⟩⟩
      · exact Or.inl a
      · exact Or.inl a
      · exact Or.inl b
      · exact Or.inr ⟨by simp [ha, hb], rfl⟩
    · rintro (a | ⟨h, e⟩)
      · exact ⟨Or.inl a, Or.inl a⟩
      · simp only [Bool.and_eq_true] at h
        exact ⟨Or.inr ⟨h.1, e⟩, Or.inr ⟨h.2, e⟩⟩
  -- `l₂ < l₁`: the first operand supplies the bound
  · have : ¬ l₁ < l₂ := not_lt_of_gt h
    simp only [this, h, if_true, if_false, max_eq_left h.le]
    constructor
    · rintro ⟨a, b⟩
      exact a
    · intro a
      refine ⟨a, ?_⟩
      rcases a with a | ⟨ha, rfl⟩
      · exact Or.inl (h.trans a)
      · exact Or.inl h


/-- The two upper tests together are the test of the smaller bound. -/
private theorem STLInterval.rawSet_upper_and (u₁ u₂ : EReal) (rc₁ rc₂ : Bool)
    (t : EReal) : -- --- CONCL ---
    ((t < u₁ ∨ (rc₁ = true ∧ t = u₁)) ∧ (t < u₂ ∨ (rc₂ = true ∧ t = u₂))) ↔
      (t < min u₁ u₂ ∨ ((if u₁ < u₂ then rc₁ else if u₂ < u₁ then rc₂ else rc₁ && rc₂) = true ∧
        t = min u₁ u₂)) := by -- --- PROOF ---
  rcases lt_trichotomy u₁ u₂ with h | h | h
  -- `u₁ < u₂`: the first operand supplies the bound
  · have : ¬ u₂ < u₁ := not_lt_of_gt h
    simp only [this, h, if_true, if_false, min_eq_left h.le]
    constructor
    · rintro ⟨a, b⟩
      exact a
    · intro a
      refine ⟨a, ?_⟩
      rcases a with a | ⟨ha, rfl⟩
      · exact Or.inl (a.trans h)
      · exact Or.inl h
  -- `u₁ = u₂`: both flags have to hold
  · subst h
    simp only [lt_self_iff_false, if_false, min_self]
    constructor
    · rintro ⟨a | ⟨ha, rfl⟩, b | ⟨hb, e⟩⟩
      · exact Or.inl a
      · exact Or.inl a
      · exact Or.inl b
      · exact Or.inr ⟨by simp [ha, hb], rfl⟩
    · rintro (a | ⟨h, e⟩)
      · exact ⟨Or.inl a, Or.inl a⟩
      · simp only [Bool.and_eq_true] at h
        exact ⟨Or.inr ⟨h.1, e⟩, Or.inr ⟨h.2, e⟩⟩
  -- `u₂ < u₁`: the second operand supplies the bound
  · have : ¬ u₁ < u₂ := not_lt_of_gt h
    simp only [this, h, if_true, if_false, min_eq_right h.le]
    constructor
    · rintro ⟨a, b⟩
      exact b
    · intro b
      refine ⟨?_, b⟩
      rcases b with b | ⟨hb, rfl⟩
      · exact Or.inl (b.trans h)
      · exact Or.inl h


/-- The intersection of two `rawSet`s is `rawSet` of the larger lower and smaller upper bound. -/
theorem STLInterval.aux_rawSet_inter (l₁ u₁ l₂ u₂ : EReal)
    (lc₁ rc₁ lc₂ rc₂ : Bool) : -- --- CONCL ---
    rawSet l₁ u₁ lc₁ rc₁ ∩ rawSet l₂ u₂ lc₂ rc₂ =
      rawSet (max l₁ l₂) (min u₁ u₂)
        (if l₂ < l₁ then lc₁ else if l₁ < l₂ then lc₂ else lc₁ && lc₂)
        (if u₁ < u₂ then rc₁ else if u₂ < u₁ then rc₂ else rc₁ && rc₂) := by -- --- PROOF ---
  ext t
  have hl := rawSet_lower_and l₁ l₂ lc₁ lc₂ t
  have hu := rawSet_upper_and u₁ u₂ rc₁ rc₂ t
  simp only [rawSet, Set.mem_inter_iff, Set.mem_setOf_eq]
  exact and_and_and_comm.trans (and_congr hl hu)


-- =======================================  MAIN THEOREM  ======================================= --

/-- `and_` denotes the intersection of the two sets. -/
theorem STLInterval.set_and_ [ExactLe 𝕋] (I J : STLInterval 𝕋) : -- --- CONCL ---
    (I.and_ J).set = I.set ∩ J.set := by -- --- PROOF ---
  cases I with
  | empty => simp [STLInterval.and_, STLInterval.set]
  | nonempty l₁ u₁ lc₁ rc₁ _ _ _ =>
    cases J with
    | empty => simp [STLInterval.and_, STLInterval.set]
    | nonempty l₂ u₂ lc₂ rc₂ _ _ _ =>
      simp only [STLInterval.and_]
      rw [STLInterval.set_stlInterval, STLInterval.set, STLInterval.set,
        aux_rawSet_inter (toReal l₁ : ℝ) (toEReal u₁) (toReal l₂ : ℝ) (toEReal u₂)]
      -- the bounds and flags are those of the larger lower and the smaller upper bound
      congr 1
      · rw [toReal_maximum]; exact EReal.coe_strictMono.monotone.map_max
      · split_ifs with h
        · exact (min_eq_left h).symm
        · exact (min_eq_right (not_le.1 h).le).symm
      · simp only [EReal.coe_lt_coe_iff]
      · split_ifs <;> rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
