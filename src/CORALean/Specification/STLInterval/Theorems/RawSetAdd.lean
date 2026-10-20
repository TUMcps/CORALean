module

public import CORALean.Specification.STLInterval.Theorems.RawSetLowerReach
public import CORALean.Specification.STLInterval.Theorems.RawSetUpperReach
public import CORALean.Specification.STLInterval.Theorems.RawSetBoundsNe
public import CORALean.Specification.STLInterval.Theorems.RawSetOrdConnected
public import Mathlib.Analysis.Convex.Basic

@[expose] public section

/-!
# The sum of two STL intervals

For nonempty `rawSet`s the sum of the sets is `rawSet` of the sums of the bounds, an end closed
when both are. The sum set is order connected, so it is enough that it reaches below and above each
time between the new bounds (`aux_add_lowerReach`, `aux_add_upperReach`).

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
* `h` – the time is past the summed lower bound

## Conclusion
* some sum of members lies at or below the time
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped Pointwise


-- =======================================  MAIN THEOREM  ======================================= --

/-- Below the new lower bound the sum set reaches down. -/
private theorem STLInterval.rawSet_add_lowerReach {l₁ u₁ l₂ u₂ : EReal} {lc₁ rc₁ lc₂ rc₂ : Bool}
    (h₁ : (rawSet l₁ u₁ lc₁ rc₁).Nonempty) (h₂ : (rawSet l₂ u₂ lc₂ rc₂).Nonempty) (t : ℝ)
    (h : l₁ + l₂ < t ∨ ((lc₁ && lc₂) = true ∧ l₁ + l₂ = t)) :
    ∃ x ∈ rawSet l₁ u₁ lc₁ rc₁, ∃ y ∈ rawSet l₂ u₂ lc₂ rc₂, x + y ≤ t := by -- --- PROOF ---
  have n₁ := (rawSet_bounds_ne h₁).1
  have n₂ := (rawSet_bounds_ne h₂).1
  -- the lower bound of the first operand is `⊥` or a real, never `⊤`
  induction l₁ using EReal.rec with
  | bot =>
    obtain ⟨y, hy⟩ := h₂
    obtain ⟨x, hx, hxs⟩ := (rawSet_lowerReach h₁ (t - y)).2 (Or.inl (EReal.bot_lt_coe _))
    exact ⟨x, hx, y, hy, by linarith⟩
  | top => exact absurd rfl n₁
  | coe a =>
    -- both lower bounds real: a third of the gap below the time on each side
    induction l₂ using EReal.rec with
    | bot =>
      obtain ⟨x, hx⟩ := h₁
      obtain ⟨y, hy, hys⟩ := (rawSet_lowerReach h₂ (t - x)).2 (Or.inl (EReal.bot_lt_coe _))
      exact ⟨x, hx, y, hy, by linarith⟩
    | top => exact absurd rfl n₂
    | coe b =>
      rw [← EReal.coe_add] at h
      rcases h with h | ⟨hc, h⟩
      · have hlt := EReal.coe_lt_coe_iff.1 h
        obtain ⟨x, hx, hxs⟩ := (rawSet_lowerReach h₁ (a + (t - a - b) / 3)).2
          (Or.inl (EReal.coe_lt_coe_iff.2 (by linarith)))
        obtain ⟨y, hy, hys⟩ := (rawSet_lowerReach h₂ (b + (t - a - b) / 3)).2
          (Or.inl (EReal.coe_lt_coe_iff.2 (by linarith)))
        exact ⟨x, hx, y, hy, by linarith⟩
      · have hab := EReal.coe_eq_coe_iff.1 h
        simp only [Bool.and_eq_true] at hc
        obtain ⟨x, hx, hxs⟩ := (rawSet_lowerReach h₁ a).2 (Or.inr ⟨hc.1, rfl⟩)
        obtain ⟨y, hy, hys⟩ := (rawSet_lowerReach h₂ b).2 (Or.inr ⟨hc.2, rfl⟩)
        exact ⟨x, hx, y, hy, by linarith⟩

/-- Before the new upper bound the sum set reaches up. -/
private theorem STLInterval.rawSet_add_upperReach {l₁ u₁ l₂ u₂ : EReal} {lc₁ rc₁ lc₂ rc₂ : Bool}
    (h₁ : (rawSet l₁ u₁ lc₁ rc₁).Nonempty) (h₂ : (rawSet l₂ u₂ lc₂ rc₂).Nonempty) (t : ℝ)
    (h : (t : EReal) < u₁ + u₂ ∨ ((rc₁ && rc₂) = true ∧ (t : EReal) = u₁ + u₂)) :
    ∃ x ∈ rawSet l₁ u₁ lc₁ rc₁, ∃ y ∈ rawSet l₂ u₂ lc₂ rc₂, t ≤ x + y := by -- --- PROOF ---
  have n₁ := (rawSet_bounds_ne h₁).2
  have n₂ := (rawSet_bounds_ne h₂).2
  -- the same for the upper bounds, `⊤` or a real
  induction u₁ using EReal.rec with
  | top =>
    obtain ⟨y, hy⟩ := h₂
    obtain ⟨x, hx, hxs⟩ := (rawSet_upperReach h₁ (t - y)).2 (Or.inl (EReal.coe_lt_top _))
    exact ⟨x, hx, y, hy, by linarith⟩
  | bot => exact absurd rfl n₁
  | coe a =>
    -- both upper bounds real: a third of the gap above the time on each side
    induction u₂ using EReal.rec with
    | top =>
      obtain ⟨x, hx⟩ := h₁
      obtain ⟨y, hy, hys⟩ := (rawSet_upperReach h₂ (t - x)).2 (Or.inl (EReal.coe_lt_top _))
      exact ⟨x, hx, y, hy, by linarith⟩
    | bot => exact absurd rfl n₂
    | coe b =>
      rw [← EReal.coe_add] at h
      rcases h with h | ⟨hc, h⟩
      · have hlt := EReal.coe_lt_coe_iff.1 h
        obtain ⟨x, hx, hxs⟩ := (rawSet_upperReach h₁ (a - (a + b - t) / 3)).2
          (Or.inl (EReal.coe_lt_coe_iff.2 (by linarith)))
        obtain ⟨y, hy, hys⟩ := (rawSet_upperReach h₂ (b - (a + b - t) / 3)).2
          (Or.inl (EReal.coe_lt_coe_iff.2 (by linarith)))
        exact ⟨x, hx, y, hy, by linarith⟩
      · have hab := EReal.coe_eq_coe_iff.1 h
        simp only [Bool.and_eq_true] at hc
        obtain ⟨x, hx, hxs⟩ := (rawSet_upperReach h₁ a).2 (Or.inr ⟨hc.1, rfl⟩)
        obtain ⟨y, hy, hys⟩ := (rawSet_upperReach h₂ b).2 (Or.inr ⟨hc.2, rfl⟩)
        exact ⟨x, hx, y, hy, by linarith⟩

/-- `rawSet (l₁+l₂) (u₁+u₂) (lc₁&&lc₂) (rc₁&&rc₂)` is the sum of two nonempty `rawSet`s. -/
theorem STLInterval.rawSet_add {l₁ u₁ l₂ u₂ : EReal} {lc₁ rc₁ lc₂ rc₂ : Bool}
    (h₁ : (rawSet l₁ u₁ lc₁ rc₁).Nonempty) (h₂ : (rawSet l₂ u₂ lc₂ rc₂).Nonempty) :
    rawSet (l₁ + l₂) (u₁ + u₂) (lc₁ && lc₂) (rc₁ && rc₂) =
      rawSet l₁ u₁ lc₁ rc₁ + rawSet l₂ u₂ lc₂ rc₂ := by -- --- PROOF ---
  -- the sum set is convex, so order connected
  have hconv : (rawSet l₁ u₁ lc₁ rc₁ + rawSet l₂ u₂ lc₂ rc₂).OrdConnected := by
    refine Convex.ordConnected ?_
    exact (convex_iff_ordConnected.2 (rawSet_ordConnected _ _ _ _)).add
      (convex_iff_ordConnected.2 (rawSet_ordConnected _ _ _ _))
  -- a time of the new interval has members of the sum below and above it
  ext t
  constructor
  · rintro ⟨hl, hu⟩
    obtain ⟨x₁, hx₁, y₁, hy₁, hxy₁⟩ := rawSet_add_lowerReach h₁ h₂ t hl
    obtain ⟨x₂, hx₂, y₂, hy₂, hxy₂⟩ := rawSet_add_upperReach h₁ h₂ t hu
    exact hconv.out (Set.add_mem_add hx₁ hy₁) (Set.add_mem_add hx₂ hy₂) ⟨hxy₁, hxy₂⟩
  -- a sum of members passes both new tests
  · rintro ⟨x, hx, y, hy, rfl⟩
    show _ ∧ _
    simp only [EReal.coe_add]
    refine ⟨?_, ?_⟩
    · rcases hx.1 with a | ⟨ha, a⟩ <;> rcases hy.1 with b | ⟨hb, b⟩
      · exact Or.inl (EReal.add_lt_add a b)
      · exact Or.inl (b ▸ EReal.add_lt_add_right_coe a y)
      · exact Or.inl (a ▸ EReal.add_lt_add_left_coe b x)
      · exact Or.inr ⟨by simp [ha, hb], by rw [a, b]⟩
    · rcases hx.2 with a | ⟨ha, a⟩ <;> rcases hy.2 with b | ⟨hb, b⟩
      · exact Or.inl (EReal.add_lt_add a b)
      · exact Or.inl (b ▸ EReal.add_lt_add_right_coe a y)
      · exact Or.inl (a ▸ EReal.add_lt_add_left_coe b x)
      · exact Or.inr ⟨by simp [ha, hb], by rw [a, b]⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
