module

public import CORALean.Specification.STLInterval.Theorems.RawSetLowerReach
public import CORALean.Specification.STLInterval.Theorems.RawSetUpperReach
public import CORALean.Specification.STLInterval.Theorems.RawSetBoundsNe

@[expose] public section

/-!
# The Minkowski difference of two STL intervals

`{t | 0 ≤ t ∧ t + J ⊆ I}` for nonempty `rawSet`s is `rawSet (lb) (ub)`, `lb = l₁ - l₂`,
`ub = u₁ - u₂` (`+∞` for two unbounded operands), an end closed when `I`'s is or `J`'s is open,
and a negative `lb` cut to the closed `0`. The lower and the upper test are proved apart.

## Inputs
* `l₁` – lower bound of the first interval
* `u₁` – upper bound of the first interval
* `l₂` – lower bound of the second interval
* `u₂` – upper bound of the second interval
* `lc₁` – first lower bound is closed
* `rc₁` – first upper bound is closed
* `lc₂` – second lower bound is closed
* `rc₂` – second upper bound is closed
* `t` – time

## Hypotheses
* `h₁` – the first interval is nonempty
* `h₂` – the second interval is nonempty

## Conclusion
* the shifted second interval stays above the first iff the time passes the difference
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- `t + J` stays above `I`'s lower end iff `t` passes `l₁ - l₂`. -/
private theorem STLInterval.rawSet_minkDiff_lower {l₁ u₁ l₂ u₂ : EReal} {lc₁ rc₁ lc₂ rc₂ : Bool}
    (h₁ : (rawSet l₁ u₁ lc₁ rc₁).Nonempty) (h₂ : (rawSet l₂ u₂ lc₂ rc₂).Nonempty)
    (t : ℝ) : -- --- CONCL ---
    (∀ y ∈ rawSet l₂ u₂ lc₂ rc₂, l₁ < ↑(t + y) ∨ (lc₁ = true ∧ l₁ = ↑(t + y))) ↔
      (l₁ - l₂ < t ∨ ((lc₁ || !lc₂) = true ∧ l₁ - l₂ = t)) := by -- --- PROOF ---
  have n₁ := (rawSet_bounds_ne h₁).1
  have n₂ := (rawSet_bounds_ne h₂).1
  induction l₁ using EReal.rec with
  | bot => simp [EReal.bot_lt_coe]
  | top => exact absurd rfl n₁
  | coe a =>
    induction l₂ using EReal.rec with
    | bot =>
      -- `a - ⊥ = ⊤`: no time fits, and `S₂` reaches below any bound
      have hR : ¬ ((a : EReal) - ⊥ < t ∨ ((lc₁ || !lc₂) = true ∧ (a : EReal) - ⊥ = t)) := by
        simp
      refine iff_of_false ?_ hR
      intro h
      obtain ⟨y, hy, hys⟩ := (rawSet_lowerReach h₂ (a - t - 1)).2 (Or.inl (EReal.bot_lt_coe _))
      rcases h y hy with h | ⟨_, h⟩
      · have := EReal.coe_lt_coe_iff.1 h; linarith
      · have := EReal.coe_eq_coe_iff.1 h; linarith
    | top => exact absurd rfl n₂
    | coe b =>
      rw [← EReal.coe_sub]
      constructor
      · intro h
        -- `t` against `a - b`, with `S₂` reaching down to `b`
        rcases lt_trichotomy (a - b) t with hab | hab | hab
        · exact Or.inl (EReal.coe_lt_coe_iff.2 hab)
        · refine Or.inr ⟨?_, by rw [hab]⟩
          by_contra hc
          simp only [Bool.or_eq_true, not_or, Bool.not_eq_true', Bool.not_eq_false] at hc
          obtain ⟨y, hy, hys⟩ := (rawSet_lowerReach h₂ b).2 (Or.inr ⟨hc.2, rfl⟩)
          have hyb : y = b := by
            rcases hy.1 with h' | ⟨_, h'⟩
            · have := EReal.coe_lt_coe_iff.1 h'; linarith
            · exact (EReal.coe_eq_coe_iff.1 h').symm
          rcases h y hy with h | ⟨hc', _⟩
          · have := EReal.coe_lt_coe_iff.1 h; linarith
          · simp [hc.1] at hc'
        · exfalso
          obtain ⟨y, hy, hys⟩ := (rawSet_lowerReach h₂ (b + (a - b - t) / 2)).2
            (Or.inl (EReal.coe_lt_coe_iff.2 (by linarith)))
          rcases h y hy with h | ⟨_, h⟩
          · have := EReal.coe_lt_coe_iff.1 h; linarith
          · have := EReal.coe_eq_coe_iff.1 h; linarith
      -- conversely `t` past `a - b` keeps every member of `S₂` past `l₁`
      · intro h y hy
        rw [EReal.coe_add]
        rcases h with h | ⟨hc, h⟩
        · have h' := EReal.coe_lt_coe_iff.1 h
          rcases hy.1 with hy' | ⟨_, hy'⟩
          · have := EReal.coe_lt_coe_iff.1 hy'
            exact Or.inl (EReal.coe_lt_coe_iff.2 (by linarith))
          · have := EReal.coe_eq_coe_iff.1 hy'
            exact Or.inl (EReal.coe_lt_coe_iff.2 (by linarith))
        · have h' := EReal.coe_eq_coe_iff.1 h
          rcases hy.1 with hy' | ⟨hc2, hy'⟩
          · have := EReal.coe_lt_coe_iff.1 hy'
            exact Or.inl (by rw [← EReal.coe_add]; exact EReal.coe_lt_coe_iff.2 (by linarith))
          · have := EReal.coe_eq_coe_iff.1 hy'
            have hc1 : lc₁ = true := by simpa [hc2] using hc
            exact Or.inr ⟨hc1, by rw [← EReal.coe_add]; exact EReal.coe_eq_coe_iff.2 (by linarith)⟩

/-- `t + J` stays below `I`'s upper end iff `t` passes `u₁ - u₂`. -/
private theorem STLInterval.rawSet_minkDiff_upper {l₁ u₁ l₂ u₂ : EReal} {lc₁ rc₁ lc₂ rc₂ : Bool}
    (h₁ : (rawSet l₁ u₁ lc₁ rc₁).Nonempty) (h₂ : (rawSet l₂ u₂ lc₂ rc₂).Nonempty)
    (t : ℝ) : -- --- CONCL ---
    (∀ y ∈ rawSet l₂ u₂ lc₂ rc₂, (↑(t + y) : EReal) < u₁ ∨ (rc₁ = true ∧ (↑(t + y) : EReal) = u₁)) ↔
      ((t : EReal) < (if u₁ = ⊤ ∧ u₂ = ⊤ then ⊤ else u₁ - u₂) ∨
        ((rc₁ || !rc₂) = true ∧
          (t : EReal) = (if u₁ = ⊤ ∧ u₂ = ⊤ then ⊤ else u₁ - u₂))) := by -- --- PROOF ---
  have n₁ := (rawSet_bounds_ne h₁).2
  have n₂ := (rawSet_bounds_ne h₂).2
  -- the first upper bound is `⊤` or a real, never `⊥`
  induction u₁ using EReal.rec with
  | bot => exact absurd rfl n₁
  | top =>
    induction u₂ using EReal.rec with
    | bot => exact absurd rfl n₂
    | top =>
      exact iff_of_true (fun y _ => Or.inl (EReal.coe_lt_top _)) (by simp [EReal.coe_lt_top])
    | coe b =>
      exact iff_of_true (fun y _ => Or.inl (EReal.coe_lt_top _)) (by simp [EReal.coe_lt_top])
  | coe a =>
    -- the second upper bound is a real, or `⊤`
    induction u₂ using EReal.rec with
    | bot => exact absurd rfl n₂
    | top =>
      have hR : ¬ ((t : EReal) <
          (if (a : EReal) = ⊤ ∧ (⊤ : EReal) = ⊤ then ⊤ else (a : EReal) - ⊤) ∨
          ((rc₁ || !rc₂) = true ∧
            (t : EReal) = (if (a : EReal) = ⊤ ∧ (⊤ : EReal) = ⊤ then ⊤ else (a : EReal) - ⊤))) := by
        simp
      refine iff_of_false ?_ hR
      intro h
      obtain ⟨y, hy, hys⟩ := (rawSet_upperReach h₂ (a - t + 1)).2 (Or.inl (EReal.coe_lt_top _))
      rcases h y hy with h | ⟨_, h⟩
      · have := EReal.coe_lt_coe_iff.1 h; linarith
      · have := EReal.coe_eq_coe_iff.1 h; linarith
    | coe b =>
      simp only [EReal.coe_ne_top, false_and, if_false]
      rw [← EReal.coe_sub]
      -- both real: the same argument as for the lower bound
      constructor
      · intro h
        -- `t` against `a - b`, with `S₂` reaching up to `b`
        rcases lt_trichotomy t (a - b) with hab | hab | hab
        · exact Or.inl (EReal.coe_lt_coe_iff.2 hab)
        · refine Or.inr ⟨?_, by rw [hab]⟩
          by_contra hc
          simp only [Bool.or_eq_true, not_or, Bool.not_eq_true', Bool.not_eq_false] at hc
          obtain ⟨y, hy, hys⟩ := (rawSet_upperReach h₂ b).2 (Or.inr ⟨hc.2, rfl⟩)
          have hyb : y = b := by
            rcases hy.2 with h' | ⟨_, h'⟩
            · have := EReal.coe_lt_coe_iff.1 h'; linarith
            · exact (EReal.coe_eq_coe_iff.1 h')
          rcases h y hy with h | ⟨hc', _⟩
          · have := EReal.coe_lt_coe_iff.1 h; linarith
          · simp [hc.1] at hc'
        · exfalso
          obtain ⟨y, hy, hys⟩ := (rawSet_upperReach h₂ (b - (t - (a - b)) / 2)).2
            (Or.inl (EReal.coe_lt_coe_iff.2 (by linarith)))
          rcases h y hy with h | ⟨_, h⟩
          · have := EReal.coe_lt_coe_iff.1 h; linarith
          · have := EReal.coe_eq_coe_iff.1 h; linarith
      -- conversely `t` before `a - b` keeps every member of `S₂` before `u₁`
      · intro h y hy
        rw [EReal.coe_add]
        rcases h with h | ⟨hc, h⟩
        · have h' := EReal.coe_lt_coe_iff.1 h
          rcases hy.2 with hy' | ⟨_, hy'⟩
          · have := EReal.coe_lt_coe_iff.1 hy'
            exact Or.inl (by rw [← EReal.coe_add]; exact EReal.coe_lt_coe_iff.2 (by linarith))
          · have := EReal.coe_eq_coe_iff.1 hy'
            exact Or.inl (by rw [← EReal.coe_add]; exact EReal.coe_lt_coe_iff.2 (by linarith))
        · have h' := EReal.coe_eq_coe_iff.1 h
          rcases hy.2 with hy' | ⟨hc2, hy'⟩
          · have := EReal.coe_lt_coe_iff.1 hy'
            exact Or.inl (by rw [← EReal.coe_add]; exact EReal.coe_lt_coe_iff.2 (by linarith))
          · have := EReal.coe_eq_coe_iff.1 hy'
            have hc1 : rc₁ = true := by simpa [hc2] using hc
            exact Or.inr ⟨hc1, by rw [← EReal.coe_add]; exact EReal.coe_eq_coe_iff.2 (by linarith)⟩

/-- The times `t ≥ 0` with `t + J ⊆ I` form `rawSet` of the difference of the bounds. -/
theorem STLInterval.rawSet_minkDiff {l₁ u₁ l₂ u₂ : EReal} {lc₁ rc₁ lc₂ rc₂ : Bool}
    (h₁ : (rawSet l₁ u₁ lc₁ rc₁).Nonempty) (h₂ : (rawSet l₂ u₂ lc₂ rc₂).Nonempty) : -- --- CONCL ---
    {t : ℝ | 0 ≤ t ∧ ∀ y ∈ rawSet l₂ u₂ lc₂ rc₂, t + y ∈ rawSet l₁ u₁ lc₁ rc₁} =
      rawSet (if l₁ - l₂ < 0 then 0 else l₁ - l₂)
        (if u₁ = ⊤ ∧ u₂ = ⊤ then ⊤ else u₁ - u₂)
        (if l₁ - l₂ < 0 then true else lc₁ || !lc₂) (rc₁ || !rc₂) := by -- --- PROOF ---
  ext t
  -- `t + y ∈ S₁` is the lower test and the upper test, for every `y`
  have hall : (∀ y ∈ rawSet l₂ u₂ lc₂ rc₂, t + y ∈ rawSet l₁ u₁ lc₁ rc₁) ↔
      (l₁ - l₂ < t ∨ ((lc₁ || !lc₂) = true ∧ l₁ - l₂ = t)) ∧
      ((t : EReal) < (if u₁ = ⊤ ∧ u₂ = ⊤ then ⊤ else u₁ - u₂) ∨
        ((rc₁ || !rc₂) = true ∧
          (t : EReal) = (if u₁ = ⊤ ∧ u₂ = ⊤ then ⊤ else u₁ - u₂))) := by
    rw [← rawSet_minkDiff_lower h₁ h₂ t, ← rawSet_minkDiff_upper h₁ h₂ t]
    exact ⟨fun h => ⟨fun y hy => (h y hy).1, fun y hy => (h y hy).2⟩,
      fun h y hy => ⟨h.1 y hy, h.2 y hy⟩⟩
  rw [Set.mem_setOf_eq, hall]
  -- cutting at `0` or not
  by_cases hlb : l₁ - l₂ < 0
  · simp only [hlb, if_true]
    show _ ↔ ((_ ∨ _) ∧ _)
    constructor
    · rintro ⟨h0, A, B⟩
      refine ⟨?_, B⟩
      rcases h0.lt_or_eq with h | h
      · exact Or.inl (EReal.coe_pos.2 h)
      · exact Or.inr ⟨rfl, by rw [← h]; rfl⟩
    -- conversely the cut interval passes the lower test
    · rintro ⟨h | ⟨_, h⟩, B⟩
      · have h' : (0 : ℝ) < t := EReal.coe_pos.1 h
        exact ⟨h'.le, Or.inl (hlb.trans (EReal.coe_pos.2 h')), B⟩
      · have h' : (0 : ℝ) = t := by exact_mod_cast h
        exact ⟨h'.le, Or.inl (hlb.trans_le (by rw [← h']; simp)), B⟩
  · simp only [hlb, if_false]
    show _ ↔ ((_ ∨ _) ∧ _)
    constructor
    · rintro ⟨h0, A, B⟩
      exact ⟨A, B⟩
    · rintro ⟨A, B⟩
      refine ⟨?_, A, B⟩
      have hle : (0 : EReal) ≤ l₁ - l₂ := not_lt.1 hlb
      rcases A with A | ⟨_, A⟩
      · exact EReal.coe_nonneg.1 (hle.trans A.le)
      · exact EReal.coe_nonneg.1 (hle.trans A.le)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
