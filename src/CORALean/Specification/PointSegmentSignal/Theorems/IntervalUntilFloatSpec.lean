module

public import CORALean.Specification.PointSegmentSignal.Operations.IntervalUntilFloat
public import CORALean.Specification.PointSegmentSignal.Theorems.IndicatorMapTime
public import CORALean.Specification.PointSegmentSignal.Theorems.IndicatorSpec
public import CORALean.Specification.PointSegmentSignal.Theorems.SetMapTime
public import CORALean.Specification.PointSegmentSignal.Theorems.SetSpec
public import CORALean.Specification.STLInterval.Theorems.Basic
public import CORALean.Specification.STLInterval.Theorems.SetAnd
public import CORALean.Specification.STLInterval.Theorems.SetStlInterval
public import CORALean.Specification.Theorems.FoldlSetSpec

@[expose] public section

/-!
# What the until of two lists of intervals over a float scalar computes

Read as reals, `intervalUntilFloat` is a valid signal, `true` at `t ≥ 0` iff `t` lies in the
shifted interval `(shift (R & L.rightClosure) untilIntNoZero) & L.leftClosure` of some pair of
intervals, or `0` is in the until interval and `t` in an interval of `rhsInt`; the until interval
without zero denotes the times of the until interval but `0`. The shift is any function: what the
result means follows from what `shift` does (`intervalUntilFloat_inner`, `_outer`).

## Inputs
* `shift` – the difference of two time intervals
* `lhsInt` – intervals of the left signal
* `rhsInt` – intervals of the right signal
* `U` – until interval

## Hypotheses
* none

## Conclusion
* the until is valid and true exactly in the shifted intervals of the pairs
-/

-- Authors:       Claude Opus 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The zero test reads whether `0` is a time of the interval. -/
private theorem PointSegmentSignal.aux_containsZero_iff (U : STLInterval 𝕋) : -- --- CONCL ---
    PointSegmentSignal.step_containsZero U = true ↔ (0 : ℝ) ∈ U.set := by -- --- PROOF ---
  cases U with
  | empty => simp [PointSegmentSignal.step_containsZero, STLInterval.set]
  | nonempty l u lc rc _ hlt h0 =>
    simp only [PointSegmentSignal.step_containsZero, STLInterval.set, STLInterval.rawSet,
      Set.mem_setOf_eq, Bool.and_eq_true, decide_eq_true_eq, toReal_zero_eq, EReal.coe_zero]
    constructor
    · -- a closed lower end at `0` is reached, and the upper end is above it or closed at it
      rintro ⟨hlc, hl⟩
      rw [hl, EReal.coe_zero] at hlt
      refine ⟨Or.inr ⟨hlc, by rw [hl, EReal.coe_zero]⟩, ?_⟩
      rcases hlt with h | ⟨h, -, hrc⟩
      · exact Or.inl h
      · exact Or.inr ⟨hrc, h⟩
    · rintro ⟨h | ⟨hlc, hl⟩, -⟩
      · exact absurd h (not_lt.2 (by exact_mod_cast h0))
      · exact ⟨hlc, by exact_mod_cast hl⟩


/-- The until interval without zero denotes its times but `0`. -/
private theorem PointSegmentSignal.aux_set_untilIntNoZero (U : STLInterval 𝕋) : -- --- CONCL ---
    (PointSegmentSignal.step_untilIntNoZero U).set = U.set \ {0} := by -- --- PROOF ---
  unfold PointSegmentSignal.step_untilIntNoZero
  by_cases h : PointSegmentSignal.step_containsZero U = true
  · -- `0` is in the interval, so the interval starts at a closed `0`
    have h0 := (PointSegmentSignal.aux_containsZero_iff U).1 h
    rw [if_pos h]
    cases U with
    | empty => exact absurd h0 (by simp [STLInterval.set])
    | nonempty l u lc rc b c hl =>
      simp only [PointSegmentSignal.step_containsZero, Bool.and_eq_true, decide_eq_true_eq,
        toReal_zero_eq] at h
      simp only [STLInterval.supremum, Option.getD_some]
      rw [STLInterval.set_stlInterval]
      ext t
      simp only [STLInterval.set, STLInterval.rawSet, Set.mem_setOf_eq, Set.mem_sdiff,
        Set.mem_singleton_iff, h.1, h.2, toReal_zero_eq, EReal.coe_zero]
      constructor
      · rintro ⟨h1 | ⟨h1, -⟩, h2⟩
        · exact ⟨⟨Or.inl h1, h2⟩, fun e => by simp [e] at h1⟩
        · exact absurd h1 (by simp)
      · rintro ⟨⟨h1 | ⟨-, h1⟩, h2⟩, h3⟩
        · exact ⟨Or.inl h1, h2⟩
        · exact absurd (by exact_mod_cast h1.symm) h3
  · -- `0` is not in the interval
    have h0 : (0 : ℝ) ∉ U.set := fun h' => h ((PointSegmentSignal.aux_containsZero_iff U).2 h')
    rw [if_neg h]
    exact (Set.sdiff_singleton_eq_self h0).symm


/-- Setting an interval to `true` on a float signal, read as reals. -/
private theorem PointSegmentSignal.aux_set_spec (s : PointSegmentSignal 𝕋)
    (hs : (s.mapTime toReal).IsValid) (I : STLInterval 𝕋) (r : PointSegmentSignal ℝ)
    (hr : r = (s.set I true).mapTime toReal) : -- --- CONCL ---
    r.IsValid ∧ ∀ t : ℝ, 0 ≤ t → (t ∈ I.set → r.at t = true) ∧
      (t ∉ I.set → r.at t = (s.mapTime toReal).at t) := by -- --- PROOF ---
  rw [hr, PointSegmentSignal.set_mapTime, ← STLInterval.set_toRealInterval I]
  exact PointSegmentSignal.set_spec _ hs _ true


/-- Setting a nonempty interval to `true` on a float signal, read as reals; an empty one is
skipped. -/
private theorem PointSegmentSignal.aux_setNonempty_spec (s : PointSegmentSignal 𝕋)
    (hs : (s.mapTime toReal).IsValid) (Q : STLInterval 𝕋) (r : PointSegmentSignal ℝ)
    (hr : r = (match Q with | .empty => s | .nonempty .. => s.set Q true :
      PointSegmentSignal 𝕋).mapTime toReal) : -- --- CONCL ---
    r.IsValid ∧ ∀ t : ℝ, 0 ≤ t → (t ∈ Q.set → r.at t = true) ∧
      (t ∉ Q.set → r.at t = (s.mapTime toReal).at t) := by -- --- PROOF ---
  cases Q with
  | empty =>
    subst hr
    exact ⟨hs, fun t _ => ⟨fun h => absurd h (by simp [STLInterval.set]), fun _ => rfl⟩⟩
  | nonempty => exact PointSegmentSignal.aux_set_spec s hs _ r hr


-- =======================================  MAIN THEOREM  ======================================= --

theorem PointSegmentSignal.intervalUntilFloat_spec
    (shift : STLInterval 𝕋 → STLInterval 𝕋 → STLInterval 𝕋)
    (lhsInt rhsInt : List (STLInterval 𝕋)) (U : STLInterval 𝕋) : -- --- CONCL ---
    let r := (PointSegmentSignal.intervalUntilFloat shift lhsInt U rhsInt).mapTime toReal
    (PointSegmentSignal.step_untilIntNoZero U).set = U.set \ {0} ∧ r.IsValid ∧
    ∀ t : ℝ, 0 ≤ t →
      (r.at t = true ↔
        (∃ L ∈ lhsInt, ∃ R ∈ rhsInt, t ∈ (shift (R.and_ L.rightClosure)
          (PointSegmentSignal.step_untilIntNoZero U)).set ∧ t ∈ L.leftClosure.set) ∨
        (0 ∈ U.set ∧ ∃ R ∈ rhsInt, t ∈ R.set)) := by -- --- PROOF ---
  dsimp only
  refine ⟨PointSegmentSignal.aux_set_untilIntNoZero U, ?_⟩
  have h0U := PointSegmentSignal.aux_containsZero_iff U
  -- the shifted interval of a pair of intervals
  let S : STLInterval 𝕋 → STLInterval 𝕋 → STLInterval 𝕋 := fun L R =>
    shift (R.and_ L.rightClosure) (PointSegmentSignal.step_untilIntNoZero U)
  let P : STLInterval 𝕋 → STLInterval 𝕋 → STLInterval 𝕋 := fun L R => (S L R).and_ L.leftClosure
  have hP : ∀ L R : STLInterval 𝕋, ∀ t : ℝ, t ∈ (P L R).set ↔
      t ∈ (S L R).set ∧ t ∈ L.leftClosure.set := fun L R t => by
    show t ∈ ((S L R).and_ L.leftClosure).set ↔ _
    rw [STLInterval.set_and_, Set.mem_inter_iff]
  -- the step of the inner loop: set the shifted interval of a pair, unless it is empty
  let step : STLInterval 𝕋 → PointSegmentSignal 𝕋 → STLInterval 𝕋 → PointSegmentSignal 𝕋 :=
    fun L out R => match P L R with
      | .empty => out
      | .nonempty .. => out.set (P L R) true
  have hstep : ∀ (L : STLInterval 𝕋) (out : PointSegmentSignal 𝕋) (R : STLInterval 𝕋),
      (out.mapTime toReal).IsValid → ((step L out R).mapTime toReal).IsValid ∧
      ∀ t : ℝ, 0 ≤ t →
        (t ∈ (P L R).set → ((step L out R).mapTime toReal).at t = true) ∧
        (t ∉ (P L R).set → ((step L out R).mapTime toReal).at t = (out.mapTime toReal).at t) :=
    fun L out R hout => PointSegmentSignal.aux_setNonempty_spec out hout (P L R) _ rfl
  -- all pairs of intervals, one left-hand side after the other
  have hinner : ∀ L ∈ lhsInt, ∀ (out : PointSegmentSignal 𝕋), (out.mapTime toReal).IsValid →
      ((rhsInt.foldl (step L) out).mapTime toReal).IsValid ∧ ∀ t : ℝ, 0 ≤ t →
      ((∃ R ∈ rhsInt, t ∈ (P L R).set) →
        ((rhsInt.foldl (step L) out).mapTime toReal).at t = true) ∧
      ((¬ ∃ R ∈ rhsInt, t ∈ (P L R).set) →
        ((rhsInt.foldl (step L) out).mapTime toReal).at t = (out.mapTime toReal).at t) :=
    fun L _ out hout => List.foldl_set_spec
      (fun sig : PointSegmentSignal 𝕋 => (sig.mapTime toReal).IsValid)
      (fun sig t => (sig.mapTime toReal).at t) rhsInt (fun R => (P L R).set) true _
      (fun sig R _ hsig => hstep L sig R hsig) out hout
  -- the signal that is false everywhere
  set I0 : STLInterval 𝕋 := STLInterval.stlInterval (0 : 𝕋) ⊤ true true toReal_zero_eq.ge with hI0
  obtain ⟨hv0, h0⟩ := PointSegmentSignal.indicator_spec I0.toRealInterval false false
  rw [← PointSegmentSignal.indicator_mapTime] at hv0 h0
  have hf0 : ∀ t : ℝ, 0 ≤ t →
      ((PointSegmentSignal.indicator I0 false false).mapTime toReal).at t = false := fun t ht => by
    by_cases hm : t ∈ I0.toRealInterval.set
    · exact (h0 t ht).1 hm
    · exact (h0 t ht).2 hm
  -- all pairs, from the signal that is false everywhere
  obtain ⟨B, hBdef⟩ : ∃ B, B = lhsInt.foldl (fun out lhs => rhsInt.foldl (step lhs) out)
      (PointSegmentSignal.indicator I0 false false) := ⟨_, rfl⟩
  obtain ⟨hvB, hB⟩ := List.foldl_set_spec
    (fun sig : PointSegmentSignal 𝕋 => (sig.mapTime toReal).IsValid)
    (fun sig t => (sig.mapTime toReal).at t) lhsInt
    (fun L => {t | ∃ R ∈ rhsInt, t ∈ (P L R).set}) true
    (fun out lhs => rhsInt.foldl (step lhs) out)
    (fun sig L hL' hsig => by
      obtain ⟨hv, h⟩ := hinner L hL' sig hsig
      exact ⟨hv, fun t ht => h t ht⟩) _ hv0
  rw [← hBdef] at hvB hB
  -- the signal `B` is true exactly where some pair gives a shifted interval
  have hBt : ∀ t : ℝ, 0 ≤ t → ((B.mapTime toReal).at t = true ↔
      ∃ L ∈ lhsInt, ∃ R ∈ rhsInt, t ∈ (P L R).set) := by
    intro t ht
    obtain ⟨b1, b2⟩ := hB t ht
    constructor
    · intro h
      by_contra hn
      have := b2 (fun ⟨L, hL', hh⟩ => hn ⟨L, hL', hh⟩)
      rw [hf0 t ht] at this
      simp [this] at h
    · rintro ⟨L, hL', hh⟩
      exact b1 ⟨L, hL', hh⟩
  have key : PointSegmentSignal.intervalUntilFloat shift lhsInt U rhsInt =
      if PointSegmentSignal.step_containsZero U = true then
        rhsInt.foldl (fun out R => out.set R true) B else B := by
    rw [hBdef]; rfl
  rw [key]
  by_cases hc : PointSegmentSignal.step_containsZero U = true
  · -- the right-hand side intervals are set as well
    rw [if_pos hc]
    obtain ⟨hvF, hF⟩ := List.foldl_set_spec
      (fun sig : PointSegmentSignal 𝕋 => (sig.mapTime toReal).IsValid)
      (fun sig t => (sig.mapTime toReal).at t) rhsInt (fun R => R.set) true
      (fun out R => out.set R true)
      (fun sig R _ hsig => PointSegmentSignal.aux_set_spec sig hsig R _ rfl) B hvB
    refine ⟨hvF, fun t ht => ?_⟩
    -- the right-hand side intervals are set last
    obtain ⟨f1, f2⟩ := hF t ht
    constructor
    · intro h
      by_cases hr : ∃ R ∈ rhsInt, t ∈ R.set
      · exact Or.inr ⟨h0U.1 hc, hr⟩
      · left
        obtain ⟨L, hL', R, hR', hmem⟩ := (hBt t ht).1 (by rw [← f2 hr]; exact h)
        exact ⟨L, hL', R, hR', (hP L R t).1 hmem⟩
    · rintro (⟨L, hL', R, hR', hmem⟩ | ⟨-, hr⟩)
      · by_cases hr : ∃ R ∈ rhsInt, t ∈ R.set
        · exact f1 hr
        · rw [f2 hr]
          exact (hBt t ht).2 ⟨L, hL', R, hR', (hP L R t).2 hmem⟩
      · exact f1 hr
  · -- there is nothing more to set
    rw [if_neg hc]
    refine ⟨hvB, fun t ht => ?_⟩
    rw [hBt t ht]
    constructor
    · rintro ⟨L, hL', R, hR', hmem⟩
      exact Or.inl ⟨L, hL', R, hR', (hP L R t).1 hmem⟩
    · rintro (⟨L, hL', R, hR', hmem⟩ | ⟨h, -⟩)
      · exact ⟨L, hL', R, hR', (hP L R t).2 hmem⟩
      · exact absurd (h0U.2 h) hc

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
