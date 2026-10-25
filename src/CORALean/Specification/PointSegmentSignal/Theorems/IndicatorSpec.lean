module

public import CORALean.Specification.PointSegmentSignal.Operations.Indicator
public import CORALean.Specification.PointSegmentSignal.Definitions.IsValid
public import CORALean.Specification.PointSegmentSignal.Operations.At
public import CORALean.Specification.PointSegmentSignal.Operations.IndicatorBounds
public import CORALean.Specification.STLInterval.Definitions.IsInBounds
public import CORALean.Specification.STLInterval.Theorems.NotMemBoundsOfEmptyBounds
public import Mathlib.Data.List.TakeWhile
public import CORALean.Specification.STLInterval.Theorems.SetIffMemBounds
public import CORALean.Specification.STLInterval.Theorems.Basic

@[expose] public section

/-!
# An indicator signal is the indicator

`indicator(interval,val,default)` of an `stlInterval` is a valid signal
with value `val` at the times the interval denotes and `default` elsewhere.

## Inputs
* `I` – time interval
* `val` – value on the interval
* `default` – value elsewhere

## Hypotheses
* none

## Conclusion
* a valid signal that is `val` on the interval and `default` elsewhere
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
variable {T : Type} [LinearOrder T] [Zero T]

/-- The signal with the single time point `0`. -/
theorem aux_at_one (p v : Bool) (t : T) (ht : 0 ≤ t) :
    (PointSegmentSignal.mk [0] [p, v]).at t = if t = 0 then p else v := by
  simp [PointSegmentSignal.at, List.takeWhile, ht, eq_comm]


/-- The signal with time points `0` and `a`. -/
theorem aux_at_two (a : T) (p0 v0 p1 v1 : Bool) (t : T) (ht : 0 ≤ t) :
    (PointSegmentSignal.mk [0, a] [p0, v0, p1, v1]).at t =
      if t < a then (if t = 0 then p0 else v0) else if t = a then p1 else v1 := by
  by_cases h1 : a ≤ t
  · simp [PointSegmentSignal.at, List.takeWhile, ht, h1, not_lt.mpr h1, eq_comm]
  · simp [PointSegmentSignal.at, List.takeWhile, ht, h1, not_le.mp h1, eq_comm]


/-- The signal with time points `0`, `a` and `b`. -/
theorem aux_at_three (a b : T) (hab : a < b) (p0 v0 p1 v1 p2 v2 : Bool) (t : T)
    (ht : 0 ≤ t) : -- --- CONCL ---
    (PointSegmentSignal.mk [0, a, b] [p0, v0, p1, v1, p2, v2]).at t =
      if t < a then (if t = 0 then p0 else v0) else if t = a then p1
      else if t < b then v1 else if t = b then p2 else v2 := by -- --- PROOF ---
  by_cases h1 : a ≤ t
  · by_cases h2 : b ≤ t
    · simp [PointSegmentSignal.at, List.takeWhile, ht, h1, h2, not_lt.mpr h1, not_lt.mpr h2,
        eq_comm]
      intro h; subst h; exact absurd h2 (not_le.mpr hab)
    · simp [PointSegmentSignal.at, List.takeWhile, ht, h1, h2, not_lt.mpr h1, not_le.mp h2, eq_comm]
  · simp [PointSegmentSignal.at, List.takeWhile, ht, h1, not_le.mp h1, eq_comm]


/-- The one-point signal is valid. -/
theorem aux_valid_one (p v : Bool) :
    (PointSegmentSignal.mk [0] [p, v] : PointSegmentSignal T).IsValid := by
  refine ⟨by simp, by simp, by simp, by simp, ?_⟩
  intro i hi hi'; simp at hi'; omega


/-- The two-point signal is valid when its second point is not redundant. -/
theorem aux_valid_two (a : T) (ha : 0 < a) (p0 v0 p1 v1 : Bool) (h : ¬ (p1 = v1 ∧ p1 = v0)) :
    (PointSegmentSignal.mk [0, a] [p0, v0, p1, v1]).IsValid := by
  refine ⟨by simp, by simp, by simp, by simp [ha], ?_⟩
  intro i hi hi'; simp at hi'; obtain rfl : i = 1 := by omega
  simpa using h


/-- The three-point signal is valid when its inner points are not redundant. -/
theorem aux_valid_three (a b : T) (ha : 0 < a) (hab : a < b) (p0 v0 p1 v1 p2 v2 : Bool)
    (h1 : ¬ (p1 = v1 ∧ p1 = v0)) (h2 : ¬ (p2 = v2 ∧ p2 = v1)) : -- --- CONCL ---
    (PointSegmentSignal.mk [0, a, b] [p0, v0, p1, v1, p2, v2]).IsValid := by -- --- PROOF ---
  refine ⟨by simp, by simp, by simp, by simp [ha, hab, ha.trans hab], ?_⟩
  intro i hi hi'; simp at hi'
  obtain rfl | rfl : i = 1 ∨ i = 2 := by omega
  · simpa using h1
  · simpa using h2


/-- The claim of `indicator_spec` for one explicit signal. -/
def aux_Spec (lb : T) (ub : WithTop T) (lc rc : Bool) (val default : Bool)
    (s : PointSegmentSignal T) : Prop :=
  s.IsValid ∧ ∀ t : T, 0 ≤ t → (STLInterval.IsInBounds lb ub lc rc t → s.at t = val) ∧
    (¬ STLInterval.IsInBounds lb ub lc rc t → s.at t = default)


/-- An empty interval or equal values: the constant signal. -/
theorem aux_empty (lb : T) (ub : WithTop T) (lc rc : Bool) (val default : Bool)
    (h : val = default ∨ STLInterval.emptyBounds lb ub lc rc = true) : -- --- CONCL ---
    aux_Spec lb ub lc rc val default ⟨[0], [default, default]⟩ := by -- --- PROOF ---
  refine ⟨aux_valid_one _ _, fun t ht => ?_⟩
  rw [aux_at_one _ _ t ht]
  simp only [ite_self]
  refine ⟨fun hmem => ?_, fun _ => trivial⟩
  rcases h with rfl | hemp
  · rfl
  · exact absurd hmem (STLInterval.not_memBounds_of_emptyBounds _ _ _ _ t hemp)


/-- An interval starting after `0` and unbounded: two time points. -/
theorem aux_top_pos (lo : T) (lc rc : Bool) (val default : Bool) (hne : val ≠ default)
    (hlo : 0 < lo) : -- --- CONCL ---
    aux_Spec lo ⊤ lc rc val default
      ⟨[0, lo], [default, default, if lc = true then val else default, val]⟩ := by -- --- PROOF ---
  refine ⟨aux_valid_two lo hlo _ _ _ _ ?_, fun t ht => ?_⟩
  · cases val <;> cases default <;> cases lc <;> simp_all
  · rw [aux_at_two lo _ _ _ _ t ht]
    rcases lt_trichotomy t lo with h | rfl | h <;> cases val <;> cases default <;> cases lc <;>
      simp_all [STLInterval.IsInBounds, le_of_lt, ne_of_lt, ne_of_gt]


/-- An interval starting at `0` and unbounded: one time point. -/
theorem aux_top_zero (lc rc : Bool) (val default : Bool) (hne : val ≠ default) :
    aux_Spec (0 : T) ⊤ lc rc val default
      ⟨[0], [if lc = true then val else default, val]⟩ := by
  refine ⟨aux_valid_one _ _, fun t ht => ?_⟩
  rw [aux_at_one _ _ t ht]
  rcases ht.lt_or_eq with h | rfl <;> cases val <;> cases default <;> cases lc <;>
    simp_all [STLInterval.IsInBounds, ne_of_gt]


/-- A single time after `0`: two time points. -/
theorem aux_eq_pos (lo : T) (val default : Bool) (hne : val ≠ default)
    (hlo : 0 < lo) : -- --- CONCL ---
    aux_Spec lo (lo : WithTop T) true true val default
      ⟨[0, lo], [default, default, val, default]⟩ := by -- --- PROOF ---
  refine ⟨aux_valid_two lo hlo _ _ _ _ ?_, fun t ht => ?_⟩
  · cases val <;> cases default <;> simp_all
  · rw [aux_at_two lo _ _ _ _ t ht]
    rcases lt_trichotomy t lo with h | rfl | h <;> cases val <;> cases default <;>
      simp_all [STLInterval.IsInBounds, le_of_lt, ne_of_lt, ne_of_gt]


/-- The time `0` alone: one time point. -/
theorem aux_eq_zero (val default : Bool) (hne : val ≠ default) :
    aux_Spec (0 : T) ((0 : T) : WithTop T) true true val default
      ⟨[0], [val, default]⟩ := by
  refine ⟨aux_valid_one _ _, fun t ht => ?_⟩
  rw [aux_at_one _ _ t ht]
  rcases ht.lt_or_eq with h | rfl <;> cases val <;> cases default <;>
    simp_all [STLInterval.IsInBounds, ne_of_gt]

end


section
variable {T : Type} [LinearOrder T] [Zero T]
set_option maxHeartbeats 120000 in -- many cases
/-- A bounded interval starting after `0`: three time points. -/
theorem aux_lt_pos (lo s : T) (lc rc : Bool) (val default : Bool) (hne : val ≠ default)
    (hlo : 0 < lo) (hls : lo < s) : -- --- CONCL ---
    aux_Spec lo (s : WithTop T) lc rc val default
      ⟨[0, lo, s], [default, default, if lc = true then val else default, val,
        if rc = true then val else default, default]⟩ := by -- --- PROOF ---
  refine ⟨aux_valid_three lo s hlo hls _ _ _ _ _ _ ?_ ?_, fun t ht => ?_⟩
  · cases val <;> cases default <;> cases lc <;> simp_all
  · cases val <;> cases default <;> cases rc <;> simp_all
  · rw [aux_at_three lo s hls _ _ _ _ _ _ t ht]
    rcases lt_trichotomy t lo with h | rfl | h
    · cases val <;> cases default <;> cases lc <;> cases rc <;>
        simp_all [STLInterval.IsInBounds, le_of_lt, ne_of_lt, ne_of_gt]
    · cases val <;> cases default <;> cases lc <;> cases rc <;>
        simp_all [STLInterval.IsInBounds, le_of_lt, ne_of_lt, ne_of_gt]
    · rcases lt_trichotomy t s with h' | rfl | h' <;> cases val <;> cases default <;>
        cases lc <;> cases rc <;> simp_all [STLInterval.IsInBounds, le_of_lt, ne_of_lt, ne_of_gt]


/-- A bounded interval starting at `0`: two time points. -/
theorem aux_lt_zero (s : T) (lc rc : Bool) (val default : Bool) (hne : val ≠ default)
    (hs : 0 < s) : -- --- CONCL ---
    aux_Spec (0 : T) (s : WithTop T) lc rc val default
      ⟨[0, s], [if lc = true then val else default, val,
        if rc = true then val else default, default]⟩ := by -- --- PROOF ---
  refine ⟨aux_valid_two s hs _ _ _ _ ?_, fun t ht => ?_⟩
  · cases val <;> cases default <;> cases rc <;> simp_all
  · rw [aux_at_two s _ _ _ _ t ht]
    rcases lt_trichotomy t s with h | rfl | h <;> rcases ht.lt_or_eq with h0 | rfl <;>
      cases val <;> cases default <;> cases lc <;> cases rc <;>
      simp_all [STLInterval.IsInBounds, le_of_lt, ne_of_lt, ne_of_gt]


/-- An indicator signal is the indicator. -/
theorem PointSegmentSignal.aux_indicatorBounds_spec {T : Type} [LinearOrder T] [Zero T] (lo : T)
    (up : WithTop T) (lc rc : Bool) (hI : 0 ≤ lo) (val default : Bool) : -- --- CONCL ---
    (PointSegmentSignal.indicatorBounds lo up lc rc val default).IsValid ∧ ∀ t : T, 0 ≤ t →
      (STLInterval.IsInBounds lo up lc rc t →
        (PointSegmentSignal.indicatorBounds lo up lc rc val default).at t = val) ∧
      (¬ STLInterval.IsInBounds lo up lc rc t →
        (PointSegmentSignal.indicatorBounds lo up lc rc val default).at t =
          default) := by -- --- PROOF ---
  show aux_Spec lo up lc rc val default _
  unfold PointSegmentSignal.indicatorBounds
  -- an empty interval or equal values: the constant signal
  by_cases h : val = default ∨ STLInterval.emptyBounds lo up lc rc = true
  · simp only [h, if_true]; exact aux_empty _ _ _ _ _ _ h
  simp only [h, if_false]
  have hne : val ≠ default := fun e => h (Or.inl e)
  have hemp : STLInterval.emptyBounds lo up lc rc = false := by
    cases e : STLInterval.emptyBounds lo up lc rc <;> simp_all
  simp only [TimeOrder.isEqvTop_iff_eq, STLInterval.emptyBounds] at hemp
  split_ifs at hemp with hh
  clear h
  induction up using WithTop.recTopCoe with
  | top =>
    -- an unbounded interval
    simp only [ne_eq, not_true_eq_false, and_false, if_false]
    rcases hI.lt_or_eq with hlo | hlo
    · simp only [hlo, if_true, List.cons_append, List.nil_append]
      exact aux_top_pos lo lc rc val default hne hlo
    · subst hlo
      simp only [lt_irrefl, if_false, List.nil_append, List.cons_append]
      exact aux_top_zero lc rc val default hne
  | coe s =>
    have hls : lo ≤ s := by
      by_contra hc; exact hh (Or.inl (by exact_mod_cast not_le.mp hc))
    rcases hls.lt_or_eq with hls | rfl
    · -- a bounded interval with distinct ends
      rcases hI.lt_or_eq with hlo | hlo
      · simp only [hlo, if_true, TimeOrder.isEqvTop_iff_eq, WithTop.coe_inj, hls.ne, ne_eq,
          not_false_eq_true,
          WithTop.coe_ne_top, and_self, WithTop.untopD_coe, List.cons_append, List.nil_append]
        exact aux_lt_pos lo s lc rc val default hne hlo hls
      · subst hlo
        simp only [lt_irrefl, if_false, TimeOrder.isEqvTop_iff_eq, WithTop.coe_inj, hls.ne, ne_eq,
          not_false_eq_true,
          WithTop.coe_ne_top, and_self, if_true, WithTop.untopD_coe, List.cons_append,
          List.nil_append]
        exact aux_lt_zero s lc rc val default hne hls
    · -- a single time: both ends are closed
      have hlc : lc = true ∧ rc = true := by
        by_contra hc; exact hh (Or.inr ⟨rfl, hc⟩)
      obtain ⟨rfl, rfl⟩ := hlc
      rcases hI.lt_or_eq with hlo | hlo
      · simp only [hlo, TimeOrder.isEqvTop_iff_eq, ne_eq, not_true_eq_false, false_and, ↓reduceIte,
          WithTop.coe_ne_top, not_false_eq_true, List.cons_append, List.nil_append]
        exact aux_eq_pos lo val default hne hlo
      · subst hlo
        simp only [lt_irrefl, TimeOrder.isEqvTop_iff_eq, ne_eq, not_true_eq_false, false_and,
          ↓reduceIte, WithTop.coe_ne_top, not_false_eq_true, List.nil_append, List.cons_append]
        exact aux_eq_zero val default hne

end


-- =======================================  MAIN THEOREM  ======================================= --

theorem PointSegmentSignal.indicator_spec (I : STLInterval ℝ)
    (val default : Bool) : -- --- CONCL ---
    (PointSegmentSignal.indicator I val default).IsValid ∧ ∀ t : ℝ, 0 ≤ t →
      (t ∈ I.set → (PointSegmentSignal.indicator I val default).at t = val) ∧
      (t ∉ I.set →
        (PointSegmentSignal.indicator I val default).at t = default) := by -- --- PROOF ---
  obtain ⟨hv, h⟩ := PointSegmentSignal.aux_indicatorBounds_spec I.lowerBound I.upperBound
    I.lowerClosed I.upperClosed (STLInterval.zero_le_lowerBound I) val default
  refine ⟨hv, fun t ht => ?_⟩
  rw [STLInterval.set_iff_memBounds I t]
  exact h t ht

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
